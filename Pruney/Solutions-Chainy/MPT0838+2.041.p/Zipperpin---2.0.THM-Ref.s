%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.shxKCGRNIT

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 166 expanded)
%              Number of leaves         :   37 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  671 (1501 expanded)
%              Number of equality atoms :   39 (  65 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v4_relat_1 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['5','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_C_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    v4_relat_1 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( sk_C_2
      = ( k7_relat_1 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('24',plain,
    ( sk_C_2
    = ( k7_relat_1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = ( k9_relat_1 @ sk_C_2 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = ( k9_relat_1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k9_relat_1 @ X21 @ X22 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ sk_B_1 )
    | ( r1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    r1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','58'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','59'])).

thf('61',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','61'])).

thf('63',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ( k1_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.shxKCGRNIT
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 155 iterations in 0.053s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.50  thf(t7_xboole_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.50  thf(t49_relset_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50                    ( ![D:$i]:
% 0.21/0.50                      ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.50                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50                       ( ![D:$i]:
% 0.21/0.50                         ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.50                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.50         ((v4_relat_1 @ X25 @ X26)
% 0.21/0.50          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('3', plain, ((v4_relat_1 @ sk_C_2 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(d18_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (v4_relat_1 @ X13 @ X14)
% 0.21/0.50          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.21/0.50          | ~ (v1_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.21/0.50          | (v1_relat_1 @ X11)
% 0.21/0.50          | ~ (v1_relat_1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(fc6_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.50  thf('10', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.21/0.50        | (r2_hidden @ (sk_B @ (k1_relat_1 @ sk_C_2)) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.50  thf(t3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.50          | ~ (r2_hidden @ X6 @ X7)
% 0.21/0.50          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.50          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.21/0.50        | ~ (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A)
% 0.21/0.50        | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A)
% 0.21/0.50        | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.50  thf('20', plain, ((v4_relat_1 @ sk_C_2 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(t209_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.50       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i]:
% 0.21/0.50         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.21/0.50          | ~ (v4_relat_1 @ X23 @ X24)
% 0.21/0.50          | ~ (v1_relat_1 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_C_2) | ((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('24', plain, (((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf(t148_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i]:
% 0.21/0.50         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.21/0.50          | ~ (v1_relat_1 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C_2) = (k9_relat_1 @ sk_C_2 @ sk_A))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C_2))),
% 0.21/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('28', plain, (((k2_relat_1 @ sk_C_2) = (k9_relat_1 @ sk_C_2 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf(t151_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         (((k9_relat_1 @ X21 @ X22) != (k1_xboole_0))
% 0.21/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.21/0.50          | ~ (v1_relat_1 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C_2) != (k1_xboole_0))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C_2)
% 0.21/0.50        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C_2) != (k1_xboole_0))
% 0.21/0.50        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.50         ((v5_relat_1 @ X25 @ X27)
% 0.21/0.50          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('36', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf(d19_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (v5_relat_1 @ X15 @ X16)
% 0.21/0.50          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.21/0.50          | ~ (v1_relat_1 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('40', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ sk_B_1)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.21/0.50        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_2)) @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.50          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.21/0.50        | ~ (r1_xboole_0 @ (k2_relat_1 @ sk_C_2) @ sk_B_1)
% 0.21/0.50        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_C_2) @ sk_B_1)
% 0.21/0.50        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.50  thf(t1_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X1 @ X0) | (m1_subset_1 @ (sk_C_1 @ X0 @ X1) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X34 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X34 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2))
% 0.21/0.50          | ~ (m1_subset_1 @ X34 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ 
% 0.21/0.50               (sk_C_1 @ X0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)) @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (((r1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) @ sk_B_1)
% 0.21/0.50        | (r1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      ((r1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) @ sk_B_1)),
% 0.21/0.50      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.50         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.21/0.50          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['54', '57'])).
% 0.21/0.50  thf('59', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '58'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '59'])).
% 0.21/0.50  thf('61', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 0.21/0.50      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.50  thf('62', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '61'])).
% 0.21/0.50  thf('63', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.21/0.50          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain, (((k1_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['63', '66'])).
% 0.21/0.50  thf('68', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['62', '67'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
