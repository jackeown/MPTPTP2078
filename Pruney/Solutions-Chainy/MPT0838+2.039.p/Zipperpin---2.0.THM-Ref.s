%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SxsdRhbFaS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 193 expanded)
%              Number of leaves         :   38 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  700 (1717 expanded)
%              Number of equality atoms :   33 (  67 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ X7 @ X7 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('11',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25
        = ( k7_relat_1 @ X25 @ X26 ) )
      | ~ ( v4_relat_1 @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','33'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ X23 @ X24 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_B_1 )
    | ( r1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    r1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['49'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['57','58'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('63',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','55','56','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','66'])).

thf('68',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('75',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['23','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SxsdRhbFaS
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:54:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 175 iterations in 0.101s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.56  thf(t3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf(d1_xboole_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.56  thf(t66_xboole_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.56       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf(t49_relset_1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56                    ( ![D:$i]:
% 0.21/0.56                      ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.56                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56                       ( ![D:$i]:
% 0.21/0.56                         ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.56                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.21/0.56  thf('7', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) != (k1_xboole_0))
% 0.21/0.56          | ~ (v1_xboole_0 @ X0)
% 0.21/0.56          | ~ (v1_xboole_0 @ (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.21/0.56        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X7 : $i]: ((r1_xboole_0 @ X7 @ X7) | ((X7) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.56  thf('11', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X5 @ X3)
% 0.21/0.56          | ~ (r2_hidden @ X5 @ X6)
% 0.21/0.56          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X0)
% 0.21/0.56          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.56          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.56  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '17'])).
% 0.21/0.56  thf('19', plain, (~ (v1_xboole_0 @ (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.56         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.21/0.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf('23', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc2_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.56         ((v4_relat_1 @ X27 @ X28)
% 0.21/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.56  thf('26', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf(t209_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.56       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X25 : $i, X26 : $i]:
% 0.21/0.56         (((X25) = (k7_relat_1 @ X25 @ X26))
% 0.21/0.56          | ~ (v4_relat_1 @ X25 @ X26)
% 0.21/0.56          | ~ (v1_relat_1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc2_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.21/0.56          | (v1_relat_1 @ X13)
% 0.21/0.56          | ~ (v1_relat_1 @ X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf(fc6_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.56  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '33'])).
% 0.21/0.56  thf(t148_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X21 : $i, X22 : $i]:
% 0.21/0.56         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 0.21/0.56          | ~ (v1_relat_1 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_A))
% 0.21/0.56        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('38', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf(t151_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.56         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         (((k9_relat_1 @ X23 @ X24) != (k1_xboole_0))
% 0.21/0.56          | (r1_xboole_0 @ (k1_relat_1 @ X23) @ X24)
% 0.21/0.56          | ~ (v1_relat_1 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((((k2_relat_1 @ sk_C_1) != (k1_xboole_0))
% 0.21/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.56        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      ((((k2_relat_1 @ sk_C_1) != (k1_xboole_0))
% 0.21/0.56        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf(t1_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X1 @ X0) | (m1_subset_1 @ (sk_C @ X0 @ X1) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X36 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X36 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.21/0.56          | ~ (m1_subset_1 @ X36 @ sk_B_1))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ 
% 0.21/0.56               (sk_C @ X0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)) @ sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (((r1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_B_1)
% 0.21/0.56        | (r1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['45', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      ((r1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_B_1)),
% 0.21/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.56  thf(t69_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.56       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (r1_xboole_0 @ X9 @ X10)
% 0.21/0.56          | ~ (r1_tarski @ X9 @ X10)
% 0.21/0.56          | (v1_xboole_0 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (((v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.21/0.56        | ~ (r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) @ sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.21/0.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.56         ((v5_relat_1 @ X27 @ X29)
% 0.21/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.56  thf('59', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.21/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf(d19_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         (~ (v5_relat_1 @ X17 @ X18)
% 0.21/0.56          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.21/0.56          | ~ (v1_relat_1 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.56  thf('64', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['52', '55', '56', '63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('66', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.56        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '66'])).
% 0.21/0.56  thf('68', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.21/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (r1_xboole_0 @ X9 @ X10)
% 0.21/0.56          | ~ (r1_tarski @ X9 @ X10)
% 0.21/0.56          | (v1_xboole_0 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 0.21/0.56        | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.56  thf('71', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf(d18_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.56  thf('72', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (v4_relat_1 @ X15 @ X16)
% 0.21/0.56          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.21/0.56          | ~ (v1_relat_1 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.56  thf('74', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('75', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.56  thf('76', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['70', '75'])).
% 0.21/0.56  thf('77', plain, ($false), inference('demod', [status(thm)], ['23', '76'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
