%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qy5uxkj8Z5

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 447 expanded)
%              Number of leaves         :   37 ( 152 expanded)
%              Depth                    :   16
%              Number of atoms          :  692 (4492 expanded)
%              Number of equality atoms :   58 ( 217 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
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
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('16',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X35 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('33',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ X19 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('44',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_C_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X20 @ X21 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('50',plain,
    ( ( ( k7_relat_1 @ sk_C_1 @ sk_A )
      = ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('53',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','57'])).

thf('59',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('61',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['58','63'])).

thf('65',plain,(
    ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['24','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','65'])).

thf('67',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['58','63'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qy5uxkj8Z5
% 0.14/0.36  % Computer   : n004.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:20:54 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 95 iterations in 0.059s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.53  thf(t7_xboole_0, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.53  thf(t49_relset_1, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.53                    ( ![D:$i]:
% 0.22/0.53                      ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.53                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.53              ( ![C:$i]:
% 0.22/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.53                       ( ![D:$i]:
% 0.22/0.53                         ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.53                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc2_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.53         ((v5_relat_1 @ X26 @ X28)
% 0.22/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.53  thf('3', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf(d19_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i]:
% 0.22/0.53         (~ (v5_relat_1 @ X12 @ X13)
% 0.22/0.53          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.22/0.53          | ~ (v1_relat_1 @ X12))),
% 0.22/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc2_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.22/0.53          | (v1_relat_1 @ X10)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf(fc6_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.53  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['5', '10'])).
% 0.22/0.53  thf(d3_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ X0 @ sk_B_1)
% 0.22/0.53          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.22/0.53        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '13'])).
% 0.22/0.53  thf(t1_subset, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.22/0.53        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X35 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X35 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.22/0.53          | ~ (m1_subset_1 @ X35 @ sk_B_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      ((((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 0.22/0.53        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.22/0.53             sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.53         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.22/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.22/0.53        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['19', '22', '23'])).
% 0.22/0.53  thf(d10_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.53  thf('26', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.22/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.53         ((v4_relat_1 @ X26 @ X27)
% 0.22/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.53  thf('29', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.22/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.53  thf(t209_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X22 : $i, X23 : $i]:
% 0.22/0.53         (((X22) = (k7_relat_1 @ X22 @ X23))
% 0.22/0.53          | ~ (v4_relat_1 @ X22 @ X23)
% 0.22/0.53          | ~ (v1_relat_1 @ X22))),
% 0.22/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.53  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('33', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf(t90_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.22/0.53         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X24 : $i, X25 : $i]:
% 0.22/0.53         (((k1_relat_1 @ (k7_relat_1 @ X24 @ X25))
% 0.22/0.53            = (k3_xboole_0 @ (k1_relat_1 @ X24) @ X25))
% 0.22/0.53          | ~ (v1_relat_1 @ X24))),
% 0.22/0.53      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      ((((k1_relat_1 @ sk_C_1) = (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))
% 0.22/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.53  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (((k1_relat_1 @ sk_C_1) = (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X24 : $i, X25 : $i]:
% 0.22/0.53         (((k1_relat_1 @ (k7_relat_1 @ X24 @ X25))
% 0.22/0.53            = (k3_xboole_0 @ (k1_relat_1 @ X24) @ X25))
% 0.22/0.53          | ~ (v1_relat_1 @ X24))),
% 0.22/0.53      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.53  thf(t152_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.53            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.53            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X18 : $i, X19 : $i]:
% 0.22/0.53         (((X18) = (k1_xboole_0))
% 0.22/0.53          | ~ (v1_relat_1 @ X19)
% 0.22/0.53          | ~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.22/0.53          | ((k9_relat_1 @ X19 @ X18) != (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.22/0.53          | ~ (v1_relat_1 @ X1)
% 0.22/0.53          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) != (k1_xboole_0))
% 0.22/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.53          | ((X2) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A))
% 0.22/0.53          | ((k9_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A) @ X0) != (k1_xboole_0))
% 0.22/0.53          | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['37', '40'])).
% 0.22/0.53  thf('42', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('44', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | ((k9_relat_1 @ sk_C_1 @ X0) != (k1_xboole_0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.22/0.53  thf('47', plain,
% 0.22/0.53      ((((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)) != (k1_xboole_0))
% 0.22/0.53        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['26', '46'])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (((k1_relat_1 @ sk_C_1) = (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf(t192_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( k7_relat_1 @ B @ A ) =
% 0.22/0.53         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      (![X20 : $i, X21 : $i]:
% 0.22/0.53         (((k7_relat_1 @ X20 @ X21)
% 0.22/0.53            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21)))
% 0.22/0.53          | ~ (v1_relat_1 @ X20))),
% 0.22/0.53      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      ((((k7_relat_1 @ sk_C_1 @ sk_A)
% 0.22/0.53          = (k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))
% 0.22/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.22/0.53  thf('51', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.53      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.22/0.53  thf(t148_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i]:
% 0.22/0.53         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.22/0.53          | ~ (v1_relat_1 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))
% 0.22/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['53', '54'])).
% 0.22/0.53  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      ((((k2_relat_1 @ sk_C_1) != (k1_xboole_0))
% 0.22/0.53        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['47', '57'])).
% 0.22/0.53  thf('59', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.53  thf('61', plain,
% 0.22/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.53         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.22/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.53  thf('62', plain,
% 0.22/0.53      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.53  thf('63', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['59', '62'])).
% 0.22/0.53  thf('64', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['58', '63'])).
% 0.22/0.53  thf('65', plain, (~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1)),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['24', '64'])).
% 0.22/0.53  thf('66', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['16', '65'])).
% 0.22/0.53  thf('67', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['58', '63'])).
% 0.22/0.53  thf('68', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
