%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qhb1Tme350

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:56 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  492 (2573 expanded)
%              Number of leaves         :   56 ( 826 expanded)
%              Depth                    :   68
%              Number of atoms          : 4038 (44192 expanded)
%              Number of equality atoms :  241 (3076 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_partfun1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_partfun1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k6_partfun1 @ X0 ) )
        = ( k7_relat_1 @ sk_D @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('25',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('26',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('30',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference('sup-',[status(thm)],['4','29'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('32',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X18: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X18 ) ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('37',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['30','40'])).

thf('42',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference('sup-',[status(thm)],['4','29'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('44',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('45',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('50',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_relat_1 @ X25 ) )
      | ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','62'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k10_relat_1 @ X10 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('67',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('75',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55 )
        = ( k5_relat_1 @ X52 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','81'])).

thf('83',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','81'])).

thf('88',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('89',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['64','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('94',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['91','92','93'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('95',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('96',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('97',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) )
    | ( ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('106',plain,
    ( ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('108',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('110',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k10_relat_1 @ X10 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('113',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['86','89'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('115',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('119',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('121',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('123',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('124',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['112','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('128',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('130',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['108','111','128','129'])).

thf('131',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('133',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','81'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('135',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40 = X43 )
      | ~ ( r2_relset_1 @ X41 @ X42 @ X40 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('138',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('139',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('141',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['130','139','140'])).

thf('142',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['63','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('145',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('147',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('149',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('151',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('155',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['142','155'])).

thf('157',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['45','156'])).

thf('158',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('159',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('160',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('161',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('162',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('163',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('164',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('165',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('166',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('167',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('168',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('169',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('170',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('171',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('172',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('173',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('174',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('175',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('176',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('178',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['174','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('185',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('188',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('189',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['173','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('195',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('199',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['172','199'])).

thf('201',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('202',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('204',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['200','201','208','209','210','211'])).

thf('213',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('214',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('216',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('218',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('219',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('220',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X29 ) @ X29 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('221',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('222',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X29 ) @ X29 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('223',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v2_funct_1 @ X26 )
      | ( ( k2_relat_1 @ X26 )
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('226',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('227',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['224','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['219','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['218','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['217','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('237',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('238',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['237','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['236','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['235','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['216','246'])).

thf('248',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('249',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('250',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('251',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ X29 @ ( k2_funct_1 @ X29 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('252',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('253',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ X29 @ ( k2_funct_1 @ X29 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('255',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('256',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_partfun1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['254','257'])).

thf('259',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('260',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k10_relat_1 @ X10 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('262',plain,(
    ! [X18: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X18 ) ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['261','262'])).

thf('264',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ) @ ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) )
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['260','263'])).

thf('265',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('266',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('267',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('268',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('269',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('271',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k10_relat_1 @ X10 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('274',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['272','273','274'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['269','276'])).

thf('278',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('279',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['258','259'])).

thf('281',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['258','259'])).

thf('282',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['264','265','266','267','268','279','280','281'])).

thf('283',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('284',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('286',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['284','285','286'])).

thf('288',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['253','287'])).

thf('289',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('290',plain,(
    ! [X18: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X18 ) ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['289','290'])).

thf('292',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('293',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('294',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('295',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['288','293','294','295','296'])).

thf('298',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['250','297'])).

thf('299',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('300',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['298','299','300'])).

thf('302',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v2_funct_1 @ X27 )
      | ( ( k2_relat_1 @ X26 )
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('303',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['301','302'])).

thf('304',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('305',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('306',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('307',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('309',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['303','304','305','306','307','308'])).

thf('310',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['309'])).

thf('311',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['249','310'])).

thf('312',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('313',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['311','312','313'])).

thf('315',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['248','314'])).

thf('316',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('317',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['315','316','317'])).

thf('319',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['247','318'])).

thf('320',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['171','319'])).

thf('321',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('322',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['320','321','322'])).

thf('324',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['170','323'])).

thf('325',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('326',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['324','325','326'])).

thf('328',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('329',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['169','329'])).

thf('331',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('332',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['330','331','332','333'])).

thf('335',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['168','334'])).

thf('336',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('337',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['335','336','337'])).

thf('339',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('340',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['338','339'])).

thf('341',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('342',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('344',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['342','343'])).

thf('345',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['167','344'])).

thf('346',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('347',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('348',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('349',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['345','346','347','348','349','350'])).

thf('352',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('353',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['351','352'])).

thf('354',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('355',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['353','354'])).

thf('356',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('357',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['355','356'])).

thf('358',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['166','357'])).

thf('359',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('360',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('361',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['358','359','360','361','362'])).

thf('364',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['165','363'])).

thf('365',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('367',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['364','365','366','367','368'])).

thf('370',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['164','369'])).

thf('371',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('372',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('373',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('374',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['370','371','372','373','374'])).

thf('376',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('377',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['375','376'])).

thf('378',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['163','377'])).

thf('379',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('380',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('381',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['378','379','380','381','382'])).

thf('384',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['162','383'])).

thf('385',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['258','259'])).

thf('386',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('387',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('388',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['384','385','386','387','388'])).

thf('390',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ X29 @ ( k2_funct_1 @ X29 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('391',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['389','390'])).

thf('392',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('393',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['315','316','317'])).

thf('394',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['391','392','393'])).

thf('395',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['161','394'])).

thf('396',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('397',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['395','396','397'])).

thf('399',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','398'])).

thf('400',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('401',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['399','400','401'])).

thf('403',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('404',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['402','403'])).

thf('405',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('406',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['404','405'])).

thf('407',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['159','406'])).

thf('408',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('409',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('410',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['407','408','409'])).

thf('411',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['158','410'])).

thf('412',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('413',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['143','144'])).

thf('414',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('415',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['413','414'])).

thf('416',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('417',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['415','416'])).

thf('418',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('419',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_partfun1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('420',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['418','419'])).

thf('421',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['417','420'])).

thf('422',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('423',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('424',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('425',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['421','422','423','424'])).

thf('426',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['412','425'])).

thf('427',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('428',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('429',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['426','427','428'])).

thf('430',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('431',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['411','429','430'])).

thf('432',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','431'])).

thf('433',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['432','433'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qhb1Tme350
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:52:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.74/1.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.74/1.97  % Solved by: fo/fo7.sh
% 1.74/1.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.97  % done 1870 iterations in 1.498s
% 1.74/1.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.74/1.97  % SZS output start Refutation
% 1.74/1.97  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.74/1.97  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.74/1.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.97  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.74/1.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.74/1.97  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.74/1.97  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.74/1.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.74/1.97  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.74/1.97  thf(sk_C_type, type, sk_C: $i).
% 1.74/1.97  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.74/1.97  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.74/1.97  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.74/1.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.97  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.74/1.97  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.74/1.97  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.74/1.97  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.74/1.97  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.74/1.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.74/1.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.74/1.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.74/1.97  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.97  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.74/1.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.74/1.97  thf(sk_D_type, type, sk_D: $i).
% 1.74/1.97  thf(dt_k2_subset_1, axiom,
% 1.74/1.97    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.74/1.97  thf('0', plain,
% 1.74/1.97      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.74/1.97  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.74/1.97  thf('1', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 1.74/1.97      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.74/1.97  thf('2', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.74/1.97      inference('demod', [status(thm)], ['0', '1'])).
% 1.74/1.97  thf(t3_subset, axiom,
% 1.74/1.97    (![A:$i,B:$i]:
% 1.74/1.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.74/1.97  thf('3', plain,
% 1.74/1.97      (![X2 : $i, X3 : $i]:
% 1.74/1.97         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.74/1.97      inference('cnf', [status(esa)], [t3_subset])).
% 1.74/1.97  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.74/1.97      inference('sup-', [status(thm)], ['2', '3'])).
% 1.74/1.97  thf(t36_funct_2, conjecture,
% 1.74/1.97    (![A:$i,B:$i,C:$i]:
% 1.74/1.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.74/1.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.97       ( ![D:$i]:
% 1.74/1.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.74/1.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.74/1.97           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.74/1.97               ( r2_relset_1 @
% 1.74/1.97                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.74/1.97                 ( k6_partfun1 @ A ) ) & 
% 1.74/1.97               ( v2_funct_1 @ C ) ) =>
% 1.74/1.97             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.74/1.97               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.74/1.97  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.97    (~( ![A:$i,B:$i,C:$i]:
% 1.74/1.97        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.74/1.97            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.97          ( ![D:$i]:
% 1.74/1.97            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.74/1.97                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.74/1.97              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.74/1.97                  ( r2_relset_1 @
% 1.74/1.97                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.74/1.97                    ( k6_partfun1 @ A ) ) & 
% 1.74/1.97                  ( v2_funct_1 @ C ) ) =>
% 1.74/1.97                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.74/1.97                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.74/1.97    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.74/1.97  thf('5', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf(cc2_relset_1, axiom,
% 1.74/1.97    (![A:$i,B:$i,C:$i]:
% 1.74/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.97       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.74/1.97  thf('6', plain,
% 1.74/1.97      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.74/1.97         ((v4_relat_1 @ X34 @ X35)
% 1.74/1.97          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.74/1.97      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.74/1.97  thf('7', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.74/1.97      inference('sup-', [status(thm)], ['5', '6'])).
% 1.74/1.97  thf(t209_relat_1, axiom,
% 1.74/1.97    (![A:$i,B:$i]:
% 1.74/1.97     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.74/1.97       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.74/1.97  thf('8', plain,
% 1.74/1.97      (![X11 : $i, X12 : $i]:
% 1.74/1.97         (((X11) = (k7_relat_1 @ X11 @ X12))
% 1.74/1.97          | ~ (v4_relat_1 @ X11 @ X12)
% 1.74/1.97          | ~ (v1_relat_1 @ X11))),
% 1.74/1.97      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.74/1.97  thf('9', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['7', '8'])).
% 1.74/1.97  thf('10', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf(cc1_relset_1, axiom,
% 1.74/1.97    (![A:$i,B:$i,C:$i]:
% 1.74/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.97       ( v1_relat_1 @ C ) ))).
% 1.74/1.97  thf('11', plain,
% 1.74/1.97      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.74/1.97         ((v1_relat_1 @ X31)
% 1.74/1.97          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.74/1.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.74/1.97  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.97  thf('13', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['9', '12'])).
% 1.74/1.97  thf(t148_relat_1, axiom,
% 1.74/1.97    (![A:$i,B:$i]:
% 1.74/1.97     ( ( v1_relat_1 @ B ) =>
% 1.74/1.97       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.74/1.97  thf('14', plain,
% 1.74/1.97      (![X7 : $i, X8 : $i]:
% 1.74/1.97         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.74/1.97          | ~ (v1_relat_1 @ X7))),
% 1.74/1.97      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.74/1.97  thf('15', plain,
% 1.74/1.97      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_D))),
% 1.74/1.97      inference('sup+', [status(thm)], ['13', '14'])).
% 1.74/1.97  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.97  thf('17', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['15', '16'])).
% 1.74/1.97  thf('18', plain,
% 1.74/1.97      (![X7 : $i, X8 : $i]:
% 1.74/1.97         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.74/1.97          | ~ (v1_relat_1 @ X7))),
% 1.74/1.97      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.74/1.97  thf(t79_relat_1, axiom,
% 1.74/1.97    (![A:$i,B:$i]:
% 1.74/1.97     ( ( v1_relat_1 @ B ) =>
% 1.74/1.97       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.74/1.97         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.74/1.97  thf('19', plain,
% 1.74/1.97      (![X19 : $i, X20 : $i]:
% 1.74/1.97         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 1.74/1.97          | ((k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) = (X19))
% 1.74/1.97          | ~ (v1_relat_1 @ X19))),
% 1.74/1.97      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.74/1.97  thf(redefinition_k6_partfun1, axiom,
% 1.74/1.97    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.74/1.97  thf('20', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.74/1.97  thf('21', plain,
% 1.74/1.97      (![X19 : $i, X20 : $i]:
% 1.74/1.97         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 1.74/1.97          | ((k5_relat_1 @ X19 @ (k6_partfun1 @ X20)) = (X19))
% 1.74/1.97          | ~ (v1_relat_1 @ X19))),
% 1.74/1.97      inference('demod', [status(thm)], ['19', '20'])).
% 1.74/1.97  thf('22', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.97         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 1.74/1.97          | ~ (v1_relat_1 @ X1)
% 1.74/1.97          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.74/1.97          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k6_partfun1 @ X2))
% 1.74/1.97              = (k7_relat_1 @ X1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['18', '21'])).
% 1.74/1.97  thf('23', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 1.74/1.97          | ((k5_relat_1 @ (k7_relat_1 @ sk_D @ sk_B) @ (k6_partfun1 @ X0))
% 1.74/1.97              = (k7_relat_1 @ sk_D @ sk_B))
% 1.74/1.97          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ sk_B))
% 1.74/1.97          | ~ (v1_relat_1 @ sk_D))),
% 1.74/1.97      inference('sup-', [status(thm)], ['17', '22'])).
% 1.74/1.97  thf('24', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['9', '12'])).
% 1.74/1.97  thf('25', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['9', '12'])).
% 1.74/1.97  thf('26', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['9', '12'])).
% 1.74/1.97  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.97  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.97  thf('29', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 1.74/1.97          | ((k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)) = (sk_D)))),
% 1.74/1.97      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 1.74/1.97  thf('30', plain,
% 1.74/1.97      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 1.74/1.97      inference('sup-', [status(thm)], ['4', '29'])).
% 1.74/1.97  thf(t78_relat_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( v1_relat_1 @ A ) =>
% 1.74/1.97       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.74/1.97  thf('31', plain,
% 1.74/1.97      (![X18 : $i]:
% 1.74/1.97         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X18)) @ X18) = (X18))
% 1.74/1.97          | ~ (v1_relat_1 @ X18))),
% 1.74/1.97      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.74/1.97  thf('32', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.74/1.97  thf('33', plain,
% 1.74/1.97      (![X18 : $i]:
% 1.74/1.97         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X18)) @ X18) = (X18))
% 1.74/1.97          | ~ (v1_relat_1 @ X18))),
% 1.74/1.97      inference('demod', [status(thm)], ['31', '32'])).
% 1.74/1.97  thf(t55_relat_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( v1_relat_1 @ A ) =>
% 1.74/1.97       ( ![B:$i]:
% 1.74/1.97         ( ( v1_relat_1 @ B ) =>
% 1.74/1.97           ( ![C:$i]:
% 1.74/1.97             ( ( v1_relat_1 @ C ) =>
% 1.74/1.97               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.74/1.97                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.74/1.97  thf('34', plain,
% 1.74/1.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X13)
% 1.74/1.97          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 1.74/1.97              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 1.74/1.97          | ~ (v1_relat_1 @ X15)
% 1.74/1.97          | ~ (v1_relat_1 @ X14))),
% 1.74/1.97      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.74/1.97  thf('35', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (((k5_relat_1 @ X0 @ X1)
% 1.74/1.97            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.74/1.97               (k5_relat_1 @ X0 @ X1)))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.74/1.97          | ~ (v1_relat_1 @ X1)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('sup+', [status(thm)], ['33', '34'])).
% 1.74/1.97  thf(fc4_funct_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.74/1.97       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.74/1.97  thf('36', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 1.74/1.97      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.74/1.97  thf('37', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.74/1.97  thf('38', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('39', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (((k5_relat_1 @ X0 @ X1)
% 1.74/1.97            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.74/1.97               (k5_relat_1 @ X0 @ X1)))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X1)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('demod', [status(thm)], ['35', '38'])).
% 1.74/1.97  thf('40', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X1)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ((k5_relat_1 @ X0 @ X1)
% 1.74/1.97              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.74/1.97                 (k5_relat_1 @ X0 @ X1))))),
% 1.74/1.97      inference('simplify', [status(thm)], ['39'])).
% 1.74/1.97  thf('41', plain,
% 1.74/1.97      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.74/1.97          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_D)
% 1.74/1.97        | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.74/1.97      inference('sup+', [status(thm)], ['30', '40'])).
% 1.74/1.97  thf('42', plain,
% 1.74/1.97      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 1.74/1.97      inference('sup-', [status(thm)], ['4', '29'])).
% 1.74/1.97  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.97  thf('44', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('45', plain,
% 1.74/1.97      (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 1.74/1.97      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 1.74/1.97  thf('46', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.74/1.97      inference('sup-', [status(thm)], ['5', '6'])).
% 1.74/1.97  thf(d18_relat_1, axiom,
% 1.74/1.97    (![A:$i,B:$i]:
% 1.74/1.97     ( ( v1_relat_1 @ B ) =>
% 1.74/1.97       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.74/1.97  thf('47', plain,
% 1.74/1.97      (![X5 : $i, X6 : $i]:
% 1.74/1.97         (~ (v4_relat_1 @ X5 @ X6)
% 1.74/1.97          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.74/1.97          | ~ (v1_relat_1 @ X5))),
% 1.74/1.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.74/1.97  thf('48', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.74/1.97      inference('sup-', [status(thm)], ['46', '47'])).
% 1.74/1.97  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.97  thf('50', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.74/1.97      inference('demod', [status(thm)], ['48', '49'])).
% 1.74/1.97  thf('51', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf(redefinition_k2_relset_1, axiom,
% 1.74/1.97    (![A:$i,B:$i,C:$i]:
% 1.74/1.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.97       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.74/1.97  thf('52', plain,
% 1.74/1.97      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.74/1.97         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 1.74/1.97          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.74/1.97  thf('53', plain,
% 1.74/1.97      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.74/1.97      inference('sup-', [status(thm)], ['51', '52'])).
% 1.74/1.97  thf('54', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('55', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.74/1.97      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.97  thf(t147_funct_1, axiom,
% 1.74/1.97    (![A:$i,B:$i]:
% 1.74/1.97     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.74/1.97       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.74/1.97         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.74/1.97  thf('56', plain,
% 1.74/1.97      (![X24 : $i, X25 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X24 @ (k2_relat_1 @ X25))
% 1.74/1.97          | ((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24)) = (X24))
% 1.74/1.97          | ~ (v1_funct_1 @ X25)
% 1.74/1.97          | ~ (v1_relat_1 @ X25))),
% 1.74/1.97      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.74/1.97  thf('57', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X0 @ sk_B)
% 1.74/1.97          | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97          | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['55', '56'])).
% 1.74/1.97  thf('58', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('59', plain,
% 1.74/1.97      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.74/1.97         ((v1_relat_1 @ X31)
% 1.74/1.97          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.74/1.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.74/1.97  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('62', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X0 @ sk_B)
% 1.74/1.97          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.74/1.97      inference('demod', [status(thm)], ['57', '60', '61'])).
% 1.74/1.97  thf('63', plain,
% 1.74/1.97      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.74/1.97         = (k1_relat_1 @ sk_D))),
% 1.74/1.97      inference('sup-', [status(thm)], ['50', '62'])).
% 1.74/1.97  thf(t182_relat_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( v1_relat_1 @ A ) =>
% 1.74/1.97       ( ![B:$i]:
% 1.74/1.97         ( ( v1_relat_1 @ B ) =>
% 1.74/1.97           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.74/1.97             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.74/1.97  thf('64', plain,
% 1.74/1.97      (![X9 : $i, X10 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X9)
% 1.74/1.97          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 1.74/1.97              = (k10_relat_1 @ X10 @ (k1_relat_1 @ X9)))
% 1.74/1.97          | ~ (v1_relat_1 @ X10))),
% 1.74/1.97      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.74/1.97  thf('65', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('66', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf(dt_k1_partfun1, axiom,
% 1.74/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.74/1.97     ( ( ( v1_funct_1 @ E ) & 
% 1.74/1.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.74/1.97         ( v1_funct_1 @ F ) & 
% 1.74/1.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.74/1.97       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.74/1.97         ( m1_subset_1 @
% 1.74/1.97           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.74/1.97           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.74/1.97  thf('67', plain,
% 1.74/1.97      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.74/1.97         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.74/1.97          | ~ (v1_funct_1 @ X44)
% 1.74/1.97          | ~ (v1_funct_1 @ X47)
% 1.74/1.97          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 1.74/1.97          | (m1_subset_1 @ (k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47) @ 
% 1.74/1.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X49))))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.74/1.97  thf('68', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.74/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.74/1.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.74/1.97          | ~ (v1_funct_1 @ X1)
% 1.74/1.97          | ~ (v1_funct_1 @ sk_C))),
% 1.74/1.97      inference('sup-', [status(thm)], ['66', '67'])).
% 1.74/1.97  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('70', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.74/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.74/1.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.74/1.97          | ~ (v1_funct_1 @ X1))),
% 1.74/1.97      inference('demod', [status(thm)], ['68', '69'])).
% 1.74/1.97  thf('71', plain,
% 1.74/1.97      ((~ (v1_funct_1 @ sk_D)
% 1.74/1.97        | (m1_subset_1 @ 
% 1.74/1.97           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.74/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.74/1.97      inference('sup-', [status(thm)], ['65', '70'])).
% 1.74/1.97  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('73', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('74', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf(redefinition_k1_partfun1, axiom,
% 1.74/1.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.74/1.97     ( ( ( v1_funct_1 @ E ) & 
% 1.74/1.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.74/1.97         ( v1_funct_1 @ F ) & 
% 1.74/1.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.74/1.97       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.74/1.97  thf('75', plain,
% 1.74/1.97      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 1.74/1.97         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 1.74/1.97          | ~ (v1_funct_1 @ X52)
% 1.74/1.97          | ~ (v1_funct_1 @ X55)
% 1.74/1.97          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 1.74/1.97          | ((k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55)
% 1.74/1.97              = (k5_relat_1 @ X52 @ X55)))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.74/1.97  thf('76', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.74/1.97            = (k5_relat_1 @ sk_C @ X0))
% 1.74/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ sk_C))),
% 1.74/1.97      inference('sup-', [status(thm)], ['74', '75'])).
% 1.74/1.97  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('78', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.97         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.74/1.97            = (k5_relat_1 @ sk_C @ X0))
% 1.74/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.74/1.97          | ~ (v1_funct_1 @ X0))),
% 1.74/1.97      inference('demod', [status(thm)], ['76', '77'])).
% 1.74/1.97  thf('79', plain,
% 1.74/1.97      ((~ (v1_funct_1 @ sk_D)
% 1.74/1.97        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.74/1.97            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['73', '78'])).
% 1.74/1.97  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('81', plain,
% 1.74/1.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.74/1.97         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.74/1.97      inference('demod', [status(thm)], ['79', '80'])).
% 1.74/1.97  thf('82', plain,
% 1.74/1.97      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.74/1.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.74/1.97      inference('demod', [status(thm)], ['71', '72', '81'])).
% 1.74/1.97  thf('83', plain,
% 1.74/1.97      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.74/1.97         ((v4_relat_1 @ X34 @ X35)
% 1.74/1.97          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.74/1.97      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.74/1.97  thf('84', plain, ((v4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ sk_A)),
% 1.74/1.97      inference('sup-', [status(thm)], ['82', '83'])).
% 1.74/1.97  thf('85', plain,
% 1.74/1.97      (![X5 : $i, X6 : $i]:
% 1.74/1.97         (~ (v4_relat_1 @ X5 @ X6)
% 1.74/1.97          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.74/1.97          | ~ (v1_relat_1 @ X5))),
% 1.74/1.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.74/1.97  thf('86', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.74/1.97        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A))),
% 1.74/1.97      inference('sup-', [status(thm)], ['84', '85'])).
% 1.74/1.97  thf('87', plain,
% 1.74/1.97      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.74/1.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.74/1.97      inference('demod', [status(thm)], ['71', '72', '81'])).
% 1.74/1.97  thf('88', plain,
% 1.74/1.97      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.74/1.97         ((v1_relat_1 @ X31)
% 1.74/1.97          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.74/1.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.74/1.97  thf('89', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 1.74/1.97      inference('sup-', [status(thm)], ['87', '88'])).
% 1.74/1.97  thf('90', plain,
% 1.74/1.97      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 1.74/1.97      inference('demod', [status(thm)], ['86', '89'])).
% 1.74/1.97  thf('91', plain,
% 1.74/1.97      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_D))),
% 1.74/1.97      inference('sup+', [status(thm)], ['64', '90'])).
% 1.74/1.97  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.97  thf('94', plain,
% 1.74/1.97      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)),
% 1.74/1.97      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.74/1.97  thf(t71_relat_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.74/1.97       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.74/1.97  thf('95', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 1.74/1.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.74/1.97  thf('96', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.74/1.97  thf('97', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('98', plain,
% 1.74/1.97      (![X5 : $i, X6 : $i]:
% 1.74/1.97         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.74/1.97          | (v4_relat_1 @ X5 @ X6)
% 1.74/1.97          | ~ (v1_relat_1 @ X5))),
% 1.74/1.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.74/1.97  thf('99', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X0 @ X1)
% 1.74/1.97          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.74/1.97          | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.74/1.97      inference('sup-', [status(thm)], ['97', '98'])).
% 1.74/1.97  thf('100', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('101', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.74/1.97      inference('demod', [status(thm)], ['99', '100'])).
% 1.74/1.97  thf('102', plain,
% 1.74/1.97      ((v4_relat_1 @ 
% 1.74/1.97        (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A)),
% 1.74/1.97      inference('sup-', [status(thm)], ['94', '101'])).
% 1.74/1.97  thf('103', plain,
% 1.74/1.97      (![X11 : $i, X12 : $i]:
% 1.74/1.97         (((X11) = (k7_relat_1 @ X11 @ X12))
% 1.74/1.97          | ~ (v4_relat_1 @ X11 @ X12)
% 1.74/1.97          | ~ (v1_relat_1 @ X11))),
% 1.74/1.97      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.74/1.97  thf('104', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ 
% 1.74/1.97           (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 1.74/1.97        | ((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.74/1.97            = (k7_relat_1 @ 
% 1.74/1.97               (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ 
% 1.74/1.97               sk_A)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['102', '103'])).
% 1.74/1.97  thf('105', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('106', plain,
% 1.74/1.97      (((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.74/1.97         = (k7_relat_1 @ 
% 1.74/1.97            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['104', '105'])).
% 1.74/1.97  thf('107', plain,
% 1.74/1.97      (![X7 : $i, X8 : $i]:
% 1.74/1.97         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.74/1.97          | ~ (v1_relat_1 @ X7))),
% 1.74/1.97      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.74/1.97  thf('108', plain,
% 1.74/1.97      ((((k2_relat_1 @ 
% 1.74/1.97          (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 1.74/1.97          = (k9_relat_1 @ 
% 1.74/1.97             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 1.74/1.97        | ~ (v1_relat_1 @ 
% 1.74/1.97             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))))),
% 1.74/1.97      inference('sup+', [status(thm)], ['106', '107'])).
% 1.74/1.97  thf('109', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 1.74/1.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.74/1.97  thf('110', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.74/1.97  thf('111', plain,
% 1.74/1.97      (![X17 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.74/1.97      inference('demod', [status(thm)], ['109', '110'])).
% 1.74/1.97  thf('112', plain,
% 1.74/1.97      (![X9 : $i, X10 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X9)
% 1.74/1.97          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 1.74/1.97              = (k10_relat_1 @ X10 @ (k1_relat_1 @ X9)))
% 1.74/1.97          | ~ (v1_relat_1 @ X10))),
% 1.74/1.97      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.74/1.97  thf('113', plain,
% 1.74/1.97      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 1.74/1.97      inference('demod', [status(thm)], ['86', '89'])).
% 1.74/1.97  thf('114', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.74/1.97      inference('demod', [status(thm)], ['99', '100'])).
% 1.74/1.97  thf('115', plain,
% 1.74/1.97      ((v4_relat_1 @ 
% 1.74/1.97        (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)),
% 1.74/1.97      inference('sup-', [status(thm)], ['113', '114'])).
% 1.74/1.97  thf('116', plain,
% 1.74/1.97      (![X11 : $i, X12 : $i]:
% 1.74/1.97         (((X11) = (k7_relat_1 @ X11 @ X12))
% 1.74/1.97          | ~ (v4_relat_1 @ X11 @ X12)
% 1.74/1.97          | ~ (v1_relat_1 @ X11))),
% 1.74/1.97      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.74/1.97  thf('117', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ 
% 1.74/1.97           (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 1.74/1.97        | ((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.74/1.97            = (k7_relat_1 @ 
% 1.74/1.97               (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['115', '116'])).
% 1.74/1.97  thf('118', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('119', plain,
% 1.74/1.97      (((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.74/1.97         = (k7_relat_1 @ 
% 1.74/1.97            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['117', '118'])).
% 1.74/1.97  thf('120', plain,
% 1.74/1.97      (![X7 : $i, X8 : $i]:
% 1.74/1.97         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.74/1.97          | ~ (v1_relat_1 @ X7))),
% 1.74/1.97      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.74/1.97  thf('121', plain,
% 1.74/1.97      ((((k2_relat_1 @ 
% 1.74/1.97          (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 1.74/1.97          = (k9_relat_1 @ 
% 1.74/1.97             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))
% 1.74/1.97        | ~ (v1_relat_1 @ 
% 1.74/1.97             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))))),
% 1.74/1.97      inference('sup+', [status(thm)], ['119', '120'])).
% 1.74/1.97  thf('122', plain,
% 1.74/1.97      (![X17 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.74/1.97      inference('demod', [status(thm)], ['109', '110'])).
% 1.74/1.97  thf('123', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('124', plain,
% 1.74/1.97      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.74/1.97         = (k9_relat_1 @ 
% 1.74/1.97            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['121', '122', '123'])).
% 1.74/1.97  thf('125', plain,
% 1.74/1.97      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.74/1.97          = (k9_relat_1 @ 
% 1.74/1.97             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_D))),
% 1.74/1.97      inference('sup+', [status(thm)], ['112', '124'])).
% 1.74/1.97  thf('126', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 1.74/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.97  thf('128', plain,
% 1.74/1.97      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.74/1.97         = (k9_relat_1 @ 
% 1.74/1.97            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.74/1.97  thf('129', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('130', plain,
% 1.74/1.97      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))
% 1.74/1.97         = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 1.74/1.97      inference('demod', [status(thm)], ['108', '111', '128', '129'])).
% 1.74/1.97  thf('131', plain,
% 1.74/1.97      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.74/1.97        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.74/1.97        (k6_partfun1 @ sk_A))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('132', plain,
% 1.74/1.97      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.74/1.97         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.74/1.97      inference('demod', [status(thm)], ['79', '80'])).
% 1.74/1.97  thf('133', plain,
% 1.74/1.97      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.74/1.97        (k6_partfun1 @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['131', '132'])).
% 1.74/1.97  thf('134', plain,
% 1.74/1.97      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.74/1.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.74/1.97      inference('demod', [status(thm)], ['71', '72', '81'])).
% 1.74/1.97  thf(redefinition_r2_relset_1, axiom,
% 1.74/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.97     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.74/1.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.97       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.74/1.97  thf('135', plain,
% 1.74/1.97      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.74/1.97         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.74/1.97          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.74/1.97          | ((X40) = (X43))
% 1.74/1.97          | ~ (r2_relset_1 @ X41 @ X42 @ X40 @ X43))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.74/1.97  thf('136', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.74/1.97          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.74/1.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.74/1.97      inference('sup-', [status(thm)], ['134', '135'])).
% 1.74/1.97  thf('137', plain,
% 1.74/1.97      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.74/1.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.74/1.97        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['133', '136'])).
% 1.74/1.97  thf(dt_k6_partfun1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( m1_subset_1 @
% 1.74/1.97         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.74/1.97       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.74/1.97  thf('138', plain,
% 1.74/1.97      (![X51 : $i]:
% 1.74/1.97         (m1_subset_1 @ (k6_partfun1 @ X51) @ 
% 1.74/1.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X51)))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.74/1.97  thf('139', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['137', '138'])).
% 1.74/1.97  thf('140', plain,
% 1.74/1.97      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('141', plain, (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) = (sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['130', '139', '140'])).
% 1.74/1.97  thf('142', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.74/1.97      inference('demod', [status(thm)], ['63', '141'])).
% 1.74/1.97  thf('143', plain,
% 1.74/1.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('144', plain,
% 1.74/1.97      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.74/1.97         ((v4_relat_1 @ X34 @ X35)
% 1.74/1.97          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.74/1.97      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.74/1.97  thf('145', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.74/1.97      inference('sup-', [status(thm)], ['143', '144'])).
% 1.74/1.97  thf('146', plain,
% 1.74/1.97      (![X11 : $i, X12 : $i]:
% 1.74/1.97         (((X11) = (k7_relat_1 @ X11 @ X12))
% 1.74/1.97          | ~ (v4_relat_1 @ X11 @ X12)
% 1.74/1.97          | ~ (v1_relat_1 @ X11))),
% 1.74/1.97      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.74/1.97  thf('147', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['145', '146'])).
% 1.74/1.97  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('149', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['147', '148'])).
% 1.74/1.97  thf('150', plain,
% 1.74/1.97      (![X7 : $i, X8 : $i]:
% 1.74/1.97         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 1.74/1.97          | ~ (v1_relat_1 @ X7))),
% 1.74/1.97      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.74/1.97  thf('151', plain,
% 1.74/1.97      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['149', '150'])).
% 1.74/1.97  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('153', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['151', '152'])).
% 1.74/1.97  thf('154', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.74/1.97      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.97  thf('155', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['153', '154'])).
% 1.74/1.97  thf('156', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.74/1.97      inference('sup+', [status(thm)], ['142', '155'])).
% 1.74/1.97  thf('157', plain, (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))),
% 1.74/1.97      inference('demod', [status(thm)], ['45', '156'])).
% 1.74/1.97  thf('158', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.74/1.97      inference('demod', [status(thm)], ['137', '138'])).
% 1.74/1.97  thf(dt_k2_funct_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.74/1.97       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.74/1.97         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.74/1.97  thf('159', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('160', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('161', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf(t65_funct_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.74/1.97       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.74/1.97  thf('162', plain,
% 1.74/1.97      (![X30 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X30)
% 1.74/1.97          | ((k2_funct_1 @ (k2_funct_1 @ X30)) = (X30))
% 1.74/1.97          | ~ (v1_funct_1 @ X30)
% 1.74/1.97          | ~ (v1_relat_1 @ X30))),
% 1.74/1.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.74/1.97  thf('163', plain,
% 1.74/1.97      (![X30 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X30)
% 1.74/1.97          | ((k2_funct_1 @ (k2_funct_1 @ X30)) = (X30))
% 1.74/1.97          | ~ (v1_funct_1 @ X30)
% 1.74/1.97          | ~ (v1_relat_1 @ X30))),
% 1.74/1.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.74/1.97  thf('164', plain,
% 1.74/1.97      (![X30 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X30)
% 1.74/1.97          | ((k2_funct_1 @ (k2_funct_1 @ X30)) = (X30))
% 1.74/1.97          | ~ (v1_funct_1 @ X30)
% 1.74/1.97          | ~ (v1_relat_1 @ X30))),
% 1.74/1.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.74/1.97  thf('165', plain,
% 1.74/1.97      (![X30 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X30)
% 1.74/1.97          | ((k2_funct_1 @ (k2_funct_1 @ X30)) = (X30))
% 1.74/1.97          | ~ (v1_funct_1 @ X30)
% 1.74/1.97          | ~ (v1_relat_1 @ X30))),
% 1.74/1.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.74/1.97  thf('166', plain,
% 1.74/1.97      (![X30 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X30)
% 1.74/1.97          | ((k2_funct_1 @ (k2_funct_1 @ X30)) = (X30))
% 1.74/1.97          | ~ (v1_funct_1 @ X30)
% 1.74/1.97          | ~ (v1_relat_1 @ X30))),
% 1.74/1.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.74/1.97  thf('167', plain,
% 1.74/1.97      (![X30 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X30)
% 1.74/1.97          | ((k2_funct_1 @ (k2_funct_1 @ X30)) = (X30))
% 1.74/1.97          | ~ (v1_funct_1 @ X30)
% 1.74/1.97          | ~ (v1_relat_1 @ X30))),
% 1.74/1.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.74/1.97  thf('168', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('169', plain,
% 1.74/1.97      (![X30 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X30)
% 1.74/1.97          | ((k2_funct_1 @ (k2_funct_1 @ X30)) = (X30))
% 1.74/1.97          | ~ (v1_funct_1 @ X30)
% 1.74/1.97          | ~ (v1_relat_1 @ X30))),
% 1.74/1.97      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.74/1.97  thf('170', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('171', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf(t55_funct_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.74/1.97       ( ( v2_funct_1 @ A ) =>
% 1.74/1.97         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.74/1.97           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.74/1.97  thf('172', plain,
% 1.74/1.97      (![X28 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X28)
% 1.74/1.97          | ((k2_relat_1 @ X28) = (k1_relat_1 @ (k2_funct_1 @ X28)))
% 1.74/1.97          | ~ (v1_funct_1 @ X28)
% 1.74/1.97          | ~ (v1_relat_1 @ X28))),
% 1.74/1.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.74/1.97  thf('173', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('174', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.74/1.97      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.97  thf('175', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('176', plain,
% 1.74/1.97      (![X28 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X28)
% 1.74/1.97          | ((k2_relat_1 @ X28) = (k1_relat_1 @ (k2_funct_1 @ X28)))
% 1.74/1.97          | ~ (v1_funct_1 @ X28)
% 1.74/1.97          | ~ (v1_relat_1 @ X28))),
% 1.74/1.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.74/1.97  thf('177', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.74/1.97      inference('sup-', [status(thm)], ['2', '3'])).
% 1.74/1.97  thf('178', plain,
% 1.74/1.97      (![X5 : $i, X6 : $i]:
% 1.74/1.97         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.74/1.97          | (v4_relat_1 @ X5 @ X6)
% 1.74/1.97          | ~ (v1_relat_1 @ X5))),
% 1.74/1.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.74/1.97  thf('179', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['177', '178'])).
% 1.74/1.97  thf('180', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.74/1.97      inference('sup+', [status(thm)], ['176', '179'])).
% 1.74/1.97  thf('181', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['175', '180'])).
% 1.74/1.97  thf('182', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['181'])).
% 1.74/1.97  thf('183', plain,
% 1.74/1.97      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['174', '182'])).
% 1.74/1.97  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('185', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('186', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('187', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.74/1.97      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 1.74/1.97  thf('188', plain,
% 1.74/1.97      (![X5 : $i, X6 : $i]:
% 1.74/1.97         (~ (v4_relat_1 @ X5 @ X6)
% 1.74/1.97          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.74/1.97          | ~ (v1_relat_1 @ X5))),
% 1.74/1.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.74/1.97  thf('189', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.74/1.97      inference('sup-', [status(thm)], ['187', '188'])).
% 1.74/1.97  thf('190', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.74/1.97      inference('sup-', [status(thm)], ['173', '189'])).
% 1.74/1.97  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('193', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.74/1.97      inference('demod', [status(thm)], ['190', '191', '192'])).
% 1.74/1.97  thf('194', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.74/1.97      inference('demod', [status(thm)], ['99', '100'])).
% 1.74/1.97  thf('195', plain,
% 1.74/1.97      ((v4_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ sk_B)),
% 1.74/1.97      inference('sup-', [status(thm)], ['193', '194'])).
% 1.74/1.97  thf('196', plain,
% 1.74/1.97      (![X11 : $i, X12 : $i]:
% 1.74/1.97         (((X11) = (k7_relat_1 @ X11 @ X12))
% 1.74/1.97          | ~ (v4_relat_1 @ X11 @ X12)
% 1.74/1.97          | ~ (v1_relat_1 @ X11))),
% 1.74/1.97      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.74/1.97  thf('197', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.74/1.97        | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97            = (k7_relat_1 @ 
% 1.74/1.97               (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ sk_B)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['195', '196'])).
% 1.74/1.97  thf('198', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('199', plain,
% 1.74/1.97      (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97         = (k7_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.74/1.97            sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['197', '198'])).
% 1.74/1.97  thf('200', plain,
% 1.74/1.97      ((((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97          = (k7_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['172', '199'])).
% 1.74/1.97  thf('201', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.74/1.97      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.97  thf('202', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.74/1.97      inference('sup-', [status(thm)], ['2', '3'])).
% 1.74/1.97  thf('203', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.74/1.97      inference('demod', [status(thm)], ['99', '100'])).
% 1.74/1.97  thf('204', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.74/1.97      inference('sup-', [status(thm)], ['202', '203'])).
% 1.74/1.97  thf('205', plain,
% 1.74/1.97      (![X11 : $i, X12 : $i]:
% 1.74/1.97         (((X11) = (k7_relat_1 @ X11 @ X12))
% 1.74/1.97          | ~ (v4_relat_1 @ X11 @ X12)
% 1.74/1.97          | ~ (v1_relat_1 @ X11))),
% 1.74/1.97      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.74/1.97  thf('206', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.74/1.97          | ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['204', '205'])).
% 1.74/1.97  thf('207', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('208', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 1.74/1.97      inference('demod', [status(thm)], ['206', '207'])).
% 1.74/1.97  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('211', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('212', plain,
% 1.74/1.97      (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97         = (k6_partfun1 @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)],
% 1.74/1.97                ['200', '201', '208', '209', '210', '211'])).
% 1.74/1.97  thf('213', plain,
% 1.74/1.97      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('214', plain,
% 1.74/1.97      (((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.74/1.97         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('sup+', [status(thm)], ['212', '213'])).
% 1.74/1.97  thf('215', plain,
% 1.74/1.97      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('216', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['214', '215'])).
% 1.74/1.97  thf('217', plain,
% 1.74/1.97      (![X28 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X28)
% 1.74/1.97          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 1.74/1.97          | ~ (v1_funct_1 @ X28)
% 1.74/1.97          | ~ (v1_relat_1 @ X28))),
% 1.74/1.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.74/1.97  thf('218', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('219', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf(t61_funct_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.74/1.97       ( ( v2_funct_1 @ A ) =>
% 1.74/1.97         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.74/1.97             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.74/1.97           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.74/1.97             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.74/1.97  thf('220', plain,
% 1.74/1.97      (![X29 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X29)
% 1.74/1.97          | ((k5_relat_1 @ (k2_funct_1 @ X29) @ X29)
% 1.74/1.97              = (k6_relat_1 @ (k2_relat_1 @ X29)))
% 1.74/1.97          | ~ (v1_funct_1 @ X29)
% 1.74/1.97          | ~ (v1_relat_1 @ X29))),
% 1.74/1.97      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.74/1.97  thf('221', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.74/1.97  thf('222', plain,
% 1.74/1.97      (![X29 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X29)
% 1.74/1.97          | ((k5_relat_1 @ (k2_funct_1 @ X29) @ X29)
% 1.74/1.97              = (k6_partfun1 @ (k2_relat_1 @ X29)))
% 1.74/1.97          | ~ (v1_funct_1 @ X29)
% 1.74/1.97          | ~ (v1_relat_1 @ X29))),
% 1.74/1.97      inference('demod', [status(thm)], ['220', '221'])).
% 1.74/1.97  thf(t48_funct_1, axiom,
% 1.74/1.97    (![A:$i]:
% 1.74/1.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.74/1.97       ( ![B:$i]:
% 1.74/1.97         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.74/1.97           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.74/1.97               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.74/1.97             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.74/1.97  thf('223', plain,
% 1.74/1.97      (![X26 : $i, X27 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X26)
% 1.74/1.97          | ~ (v1_funct_1 @ X26)
% 1.74/1.97          | (v2_funct_1 @ X26)
% 1.74/1.97          | ((k2_relat_1 @ X26) != (k1_relat_1 @ X27))
% 1.74/1.97          | ~ (v2_funct_1 @ (k5_relat_1 @ X26 @ X27))
% 1.74/1.97          | ~ (v1_funct_1 @ X27)
% 1.74/1.97          | ~ (v1_relat_1 @ X27))),
% 1.74/1.97      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.74/1.97  thf('224', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.74/1.97          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['222', '223'])).
% 1.74/1.97  thf('225', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 1.74/1.97      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.74/1.97  thf('226', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.74/1.97  thf('227', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 1.74/1.97      inference('demod', [status(thm)], ['225', '226'])).
% 1.74/1.97  thf('228', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.74/1.97          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.74/1.97      inference('demod', [status(thm)], ['224', '227'])).
% 1.74/1.97  thf('229', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['228'])).
% 1.74/1.97  thf('230', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.74/1.97          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['219', '229'])).
% 1.74/1.97  thf('231', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['230'])).
% 1.74/1.97  thf('232', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.74/1.97          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['218', '231'])).
% 1.74/1.97  thf('233', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['232'])).
% 1.74/1.97  thf('234', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['217', '233'])).
% 1.74/1.97  thf('235', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['234'])).
% 1.74/1.97  thf('236', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('237', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('238', plain,
% 1.74/1.97      (![X28 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X28)
% 1.74/1.97          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 1.74/1.97          | ~ (v1_funct_1 @ X28)
% 1.74/1.97          | ~ (v1_relat_1 @ X28))),
% 1.74/1.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.74/1.97  thf('239', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['181'])).
% 1.74/1.97  thf('240', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.74/1.97      inference('sup+', [status(thm)], ['238', '239'])).
% 1.74/1.97  thf('241', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['237', '240'])).
% 1.74/1.97  thf('242', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['241'])).
% 1.74/1.97  thf('243', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['236', '242'])).
% 1.74/1.97  thf('244', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['243'])).
% 1.74/1.97  thf('245', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['235', '244'])).
% 1.74/1.97  thf('246', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 1.74/1.97          | ~ (v2_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_funct_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('simplify', [status(thm)], ['245'])).
% 1.74/1.97  thf('247', plain,
% 1.74/1.97      (((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ sk_B)
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('sup+', [status(thm)], ['216', '246'])).
% 1.74/1.97  thf('248', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('249', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('250', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('251', plain,
% 1.74/1.97      (![X29 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X29)
% 1.74/1.97          | ((k5_relat_1 @ X29 @ (k2_funct_1 @ X29))
% 1.74/1.97              = (k6_relat_1 @ (k1_relat_1 @ X29)))
% 1.74/1.97          | ~ (v1_funct_1 @ X29)
% 1.74/1.97          | ~ (v1_relat_1 @ X29))),
% 1.74/1.97      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.74/1.97  thf('252', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 1.74/1.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.74/1.97  thf('253', plain,
% 1.74/1.97      (![X29 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X29)
% 1.74/1.97          | ((k5_relat_1 @ X29 @ (k2_funct_1 @ X29))
% 1.74/1.97              = (k6_partfun1 @ (k1_relat_1 @ X29)))
% 1.74/1.97          | ~ (v1_funct_1 @ X29)
% 1.74/1.97          | ~ (v1_relat_1 @ X29))),
% 1.74/1.97      inference('demod', [status(thm)], ['251', '252'])).
% 1.74/1.97  thf('254', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.74/1.97      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.97  thf('255', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.74/1.97      inference('sup-', [status(thm)], ['2', '3'])).
% 1.74/1.97  thf('256', plain,
% 1.74/1.97      (![X19 : $i, X20 : $i]:
% 1.74/1.97         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 1.74/1.97          | ((k5_relat_1 @ X19 @ (k6_partfun1 @ X20)) = (X19))
% 1.74/1.97          | ~ (v1_relat_1 @ X19))),
% 1.74/1.97      inference('demod', [status(thm)], ['19', '20'])).
% 1.74/1.97  thf('257', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['255', '256'])).
% 1.74/1.97  thf('258', plain,
% 1.74/1.97      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['254', '257'])).
% 1.74/1.97  thf('259', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('260', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.74/1.97      inference('demod', [status(thm)], ['258', '259'])).
% 1.74/1.97  thf('261', plain,
% 1.74/1.97      (![X9 : $i, X10 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X9)
% 1.74/1.97          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 1.74/1.97              = (k10_relat_1 @ X10 @ (k1_relat_1 @ X9)))
% 1.74/1.97          | ~ (v1_relat_1 @ X10))),
% 1.74/1.97      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.74/1.97  thf('262', plain,
% 1.74/1.97      (![X18 : $i]:
% 1.74/1.97         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X18)) @ X18) = (X18))
% 1.74/1.97          | ~ (v1_relat_1 @ X18))),
% 1.74/1.97      inference('demod', [status(thm)], ['31', '32'])).
% 1.74/1.97  thf('263', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (((k5_relat_1 @ 
% 1.74/1.97            (k6_partfun1 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.74/1.97            (k5_relat_1 @ X1 @ X0)) = (k5_relat_1 @ X1 @ X0))
% 1.74/1.97          | ~ (v1_relat_1 @ X1)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.74/1.97      inference('sup+', [status(thm)], ['261', '262'])).
% 1.74/1.97  thf('264', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ((k5_relat_1 @ 
% 1.74/1.97            (k6_partfun1 @ 
% 1.74/1.97             (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k6_partfun1 @ sk_B)))) @ 
% 1.74/1.97            (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))
% 1.74/1.97            = (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))))),
% 1.74/1.97      inference('sup-', [status(thm)], ['260', '263'])).
% 1.74/1.97  thf('265', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('266', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('267', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('268', plain,
% 1.74/1.97      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('269', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.74/1.97      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.97  thf('270', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['255', '256'])).
% 1.74/1.97  thf('271', plain,
% 1.74/1.97      (![X9 : $i, X10 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X9)
% 1.74/1.97          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 1.74/1.97              = (k10_relat_1 @ X10 @ (k1_relat_1 @ X9)))
% 1.74/1.97          | ~ (v1_relat_1 @ X10))),
% 1.74/1.97      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.74/1.97  thf('272', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (((k1_relat_1 @ X0)
% 1.74/1.97            = (k10_relat_1 @ X0 @ 
% 1.74/1.97               (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.74/1.97      inference('sup+', [status(thm)], ['270', '271'])).
% 1.74/1.97  thf('273', plain,
% 1.74/1.97      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('274', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('275', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('demod', [status(thm)], ['272', '273', '274'])).
% 1.74/1.97  thf('276', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.74/1.97      inference('simplify', [status(thm)], ['275'])).
% 1.74/1.97  thf('277', plain,
% 1.74/1.97      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['269', '276'])).
% 1.74/1.97  thf('278', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('279', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['277', '278'])).
% 1.74/1.97  thf('280', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.74/1.97      inference('demod', [status(thm)], ['258', '259'])).
% 1.74/1.97  thf('281', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.74/1.97      inference('demod', [status(thm)], ['258', '259'])).
% 1.74/1.97  thf('282', plain,
% 1.74/1.97      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C) = (sk_C))),
% 1.74/1.97      inference('demod', [status(thm)],
% 1.74/1.97                ['264', '265', '266', '267', '268', '279', '280', '281'])).
% 1.74/1.97  thf('283', plain,
% 1.74/1.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X13)
% 1.74/1.97          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 1.74/1.97              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 1.74/1.97          | ~ (v1_relat_1 @ X15)
% 1.74/1.97          | ~ (v1_relat_1 @ X14))),
% 1.74/1.97      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.74/1.97  thf('284', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (((k5_relat_1 @ sk_C @ X0)
% 1.74/1.97            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.74/1.97               (k5_relat_1 @ sk_C @ X0)))
% 1.74/1.97          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['282', '283'])).
% 1.74/1.97  thf('285', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('286', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('287', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (((k5_relat_1 @ sk_C @ X0)
% 1.74/1.97            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.74/1.97               (k5_relat_1 @ sk_C @ X0)))
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('demod', [status(thm)], ['284', '285', '286'])).
% 1.74/1.97  thf('288', plain,
% 1.74/1.97      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.74/1.97          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.74/1.97             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('sup+', [status(thm)], ['253', '287'])).
% 1.74/1.97  thf('289', plain,
% 1.74/1.97      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('290', plain,
% 1.74/1.97      (![X18 : $i]:
% 1.74/1.97         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X18)) @ X18) = (X18))
% 1.74/1.97          | ~ (v1_relat_1 @ X18))),
% 1.74/1.97      inference('demod', [status(thm)], ['31', '32'])).
% 1.74/1.97  thf('291', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.74/1.97            = (k6_partfun1 @ X0))
% 1.74/1.97          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.74/1.97      inference('sup+', [status(thm)], ['289', '290'])).
% 1.74/1.97  thf('292', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('293', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.74/1.97           = (k6_partfun1 @ X0))),
% 1.74/1.97      inference('demod', [status(thm)], ['291', '292'])).
% 1.74/1.97  thf('294', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('295', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('296', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('297', plain,
% 1.74/1.97      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.74/1.97          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['288', '293', '294', '295', '296'])).
% 1.74/1.97  thf('298', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.74/1.97            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.74/1.97      inference('sup-', [status(thm)], ['250', '297'])).
% 1.74/1.97  thf('299', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('300', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('301', plain,
% 1.74/1.97      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.74/1.97         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['298', '299', '300'])).
% 1.74/1.97  thf('302', plain,
% 1.74/1.97      (![X26 : $i, X27 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X26)
% 1.74/1.97          | ~ (v1_funct_1 @ X26)
% 1.74/1.97          | (v2_funct_1 @ X27)
% 1.74/1.97          | ((k2_relat_1 @ X26) != (k1_relat_1 @ X27))
% 1.74/1.97          | ~ (v2_funct_1 @ (k5_relat_1 @ X26 @ X27))
% 1.74/1.97          | ~ (v1_funct_1 @ X27)
% 1.74/1.97          | ~ (v1_relat_1 @ X27))),
% 1.74/1.97      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.74/1.97  thf('303', plain,
% 1.74/1.97      ((~ (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C))),
% 1.74/1.97      inference('sup-', [status(thm)], ['301', '302'])).
% 1.74/1.97  thf('304', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 1.74/1.97      inference('demod', [status(thm)], ['225', '226'])).
% 1.74/1.97  thf('305', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.74/1.97      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.97  thf('306', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['214', '215'])).
% 1.74/1.97  thf('307', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('308', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('309', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ((sk_B) != (sk_B))
% 1.74/1.97        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)],
% 1.74/1.97                ['303', '304', '305', '306', '307', '308'])).
% 1.74/1.97  thf('310', plain,
% 1.74/1.97      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('simplify', [status(thm)], ['309'])).
% 1.74/1.97  thf('311', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['249', '310'])).
% 1.74/1.97  thf('312', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('313', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('314', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['311', '312', '313'])).
% 1.74/1.97  thf('315', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['248', '314'])).
% 1.74/1.97  thf('316', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('317', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('318', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.74/1.97      inference('demod', [status(thm)], ['315', '316', '317'])).
% 1.74/1.97  thf('319', plain,
% 1.74/1.97      (((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ sk_B)
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['247', '318'])).
% 1.74/1.97  thf('320', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.74/1.97           sk_B))),
% 1.74/1.97      inference('sup-', [status(thm)], ['171', '319'])).
% 1.74/1.97  thf('321', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('322', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('323', plain,
% 1.74/1.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.74/1.97           sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['320', '321', '322'])).
% 1.74/1.97  thf('324', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.74/1.97           sk_B))),
% 1.74/1.97      inference('sup-', [status(thm)], ['170', '323'])).
% 1.74/1.97  thf('325', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('326', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('327', plain,
% 1.74/1.97      ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ sk_B)),
% 1.74/1.97      inference('demod', [status(thm)], ['324', '325', '326'])).
% 1.74/1.97  thf('328', plain,
% 1.74/1.97      (![X5 : $i, X6 : $i]:
% 1.74/1.97         (~ (v4_relat_1 @ X5 @ X6)
% 1.74/1.97          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.74/1.97          | ~ (v1_relat_1 @ X5))),
% 1.74/1.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.74/1.97  thf('329', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 1.74/1.97        | (r1_tarski @ 
% 1.74/1.97           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ 
% 1.74/1.97           sk_B))),
% 1.74/1.97      inference('sup-', [status(thm)], ['327', '328'])).
% 1.74/1.97  thf('330', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C)
% 1.74/1.97        | (r1_tarski @ 
% 1.74/1.97           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ 
% 1.74/1.97           sk_B))),
% 1.74/1.97      inference('sup-', [status(thm)], ['169', '329'])).
% 1.74/1.97  thf('331', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('332', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('333', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('334', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | (r1_tarski @ 
% 1.74/1.97           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ 
% 1.74/1.97           sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['330', '331', '332', '333'])).
% 1.74/1.97  thf('335', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | (r1_tarski @ 
% 1.74/1.97           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ 
% 1.74/1.97           sk_B))),
% 1.74/1.97      inference('sup-', [status(thm)], ['168', '334'])).
% 1.74/1.97  thf('336', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('337', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('338', plain,
% 1.74/1.97      ((r1_tarski @ 
% 1.74/1.97        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ sk_B)),
% 1.74/1.97      inference('demod', [status(thm)], ['335', '336', '337'])).
% 1.74/1.97  thf('339', plain,
% 1.74/1.97      (![X0 : $i, X1 : $i]:
% 1.74/1.97         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.74/1.97      inference('demod', [status(thm)], ['99', '100'])).
% 1.74/1.97  thf('340', plain,
% 1.74/1.97      ((v4_relat_1 @ 
% 1.74/1.97        (k6_partfun1 @ 
% 1.74/1.97         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))) @ 
% 1.74/1.97        sk_B)),
% 1.74/1.97      inference('sup-', [status(thm)], ['338', '339'])).
% 1.74/1.97  thf('341', plain,
% 1.74/1.97      (![X11 : $i, X12 : $i]:
% 1.74/1.97         (((X11) = (k7_relat_1 @ X11 @ X12))
% 1.74/1.97          | ~ (v4_relat_1 @ X11 @ X12)
% 1.74/1.97          | ~ (v1_relat_1 @ X11))),
% 1.74/1.97      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.74/1.97  thf('342', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ 
% 1.74/1.97           (k6_partfun1 @ 
% 1.74/1.97            (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))
% 1.74/1.97        | ((k6_partfun1 @ 
% 1.74/1.97            (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 1.74/1.97            = (k7_relat_1 @ 
% 1.74/1.97               (k6_partfun1 @ 
% 1.74/1.97                (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))) @ 
% 1.74/1.97               sk_B)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['340', '341'])).
% 1.74/1.97  thf('343', plain, (![X22 : $i]: (v1_relat_1 @ (k6_partfun1 @ X22))),
% 1.74/1.97      inference('demod', [status(thm)], ['36', '37'])).
% 1.74/1.97  thf('344', plain,
% 1.74/1.97      (((k6_partfun1 @ 
% 1.74/1.97         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 1.74/1.97         = (k7_relat_1 @ 
% 1.74/1.97            (k6_partfun1 @ 
% 1.74/1.97             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))) @ 
% 1.74/1.97            sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['342', '343'])).
% 1.74/1.97  thf('345', plain,
% 1.74/1.97      ((((k6_partfun1 @ 
% 1.74/1.97          (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 1.74/1.97          = (k7_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.74/1.97             sk_B))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['167', '344'])).
% 1.74/1.97  thf('346', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['214', '215'])).
% 1.74/1.97  thf('347', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 1.74/1.97      inference('demod', [status(thm)], ['206', '207'])).
% 1.74/1.97  thf('348', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('349', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('350', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('351', plain,
% 1.74/1.97      (((k6_partfun1 @ 
% 1.74/1.97         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 1.74/1.97         = (k6_partfun1 @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)],
% 1.74/1.97                ['345', '346', '347', '348', '349', '350'])).
% 1.74/1.97  thf('352', plain,
% 1.74/1.97      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('353', plain,
% 1.74/1.97      (((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.74/1.97         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.74/1.97      inference('sup+', [status(thm)], ['351', '352'])).
% 1.74/1.97  thf('354', plain,
% 1.74/1.97      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.74/1.97      inference('demod', [status(thm)], ['95', '96'])).
% 1.74/1.97  thf('355', plain,
% 1.74/1.97      (((sk_B)
% 1.74/1.97         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.74/1.97      inference('demod', [status(thm)], ['353', '354'])).
% 1.74/1.97  thf('356', plain,
% 1.74/1.97      (![X28 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X28)
% 1.74/1.97          | ((k2_relat_1 @ X28) = (k1_relat_1 @ (k2_funct_1 @ X28)))
% 1.74/1.97          | ~ (v1_funct_1 @ X28)
% 1.74/1.97          | ~ (v1_relat_1 @ X28))),
% 1.74/1.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.74/1.97  thf('357', plain,
% 1.74/1.97      ((((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.74/1.97      inference('sup+', [status(thm)], ['355', '356'])).
% 1.74/1.97  thf('358', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['166', '357'])).
% 1.74/1.97  thf('359', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('360', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('361', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('362', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('363', plain,
% 1.74/1.97      ((~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.74/1.97      inference('demod', [status(thm)], ['358', '359', '360', '361', '362'])).
% 1.74/1.97  thf('364', plain,
% 1.74/1.97      ((~ (v2_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C)
% 1.74/1.97        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.74/1.97      inference('sup-', [status(thm)], ['165', '363'])).
% 1.74/1.97  thf('365', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('366', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('367', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('368', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('369', plain,
% 1.74/1.97      ((((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.74/1.97      inference('demod', [status(thm)], ['364', '365', '366', '367', '368'])).
% 1.74/1.97  thf('370', plain,
% 1.74/1.97      ((~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C)
% 1.74/1.97        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['164', '369'])).
% 1.74/1.97  thf('371', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('372', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('373', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('374', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('375', plain,
% 1.74/1.97      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['370', '371', '372', '373', '374'])).
% 1.74/1.97  thf('376', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['255', '256'])).
% 1.74/1.97  thf('377', plain,
% 1.74/1.97      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.74/1.97          (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.74/1.97      inference('sup+', [status(thm)], ['375', '376'])).
% 1.74/1.97  thf('378', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C)
% 1.74/1.97        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.74/1.97            (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.74/1.97      inference('sup-', [status(thm)], ['163', '377'])).
% 1.74/1.97  thf('379', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('380', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('381', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('382', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('383', plain,
% 1.74/1.97      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k6_partfun1 @ sk_B))
% 1.74/1.97         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['378', '379', '380', '381', '382'])).
% 1.74/1.97  thf('384', plain,
% 1.74/1.97      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 1.74/1.97          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v2_funct_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['162', '383'])).
% 1.74/1.97  thf('385', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.74/1.97      inference('demod', [status(thm)], ['258', '259'])).
% 1.74/1.97  thf('386', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('387', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('388', plain, ((v2_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('389', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['384', '385', '386', '387', '388'])).
% 1.74/1.97  thf('390', plain,
% 1.74/1.97      (![X29 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X29)
% 1.74/1.97          | ((k5_relat_1 @ X29 @ (k2_funct_1 @ X29))
% 1.74/1.97              = (k6_partfun1 @ (k1_relat_1 @ X29)))
% 1.74/1.97          | ~ (v1_funct_1 @ X29)
% 1.74/1.97          | ~ (v1_relat_1 @ X29))),
% 1.74/1.97      inference('demod', [status(thm)], ['251', '252'])).
% 1.74/1.97  thf('391', plain,
% 1.74/1.97      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.74/1.97          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('sup+', [status(thm)], ['389', '390'])).
% 1.74/1.97  thf('392', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['214', '215'])).
% 1.74/1.97  thf('393', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.74/1.97      inference('demod', [status(thm)], ['315', '316', '317'])).
% 1.74/1.97  thf('394', plain,
% 1.74/1.97      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.74/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.74/1.97      inference('demod', [status(thm)], ['391', '392', '393'])).
% 1.74/1.97  thf('395', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['161', '394'])).
% 1.74/1.97  thf('396', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('397', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('398', plain,
% 1.74/1.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.74/1.97      inference('demod', [status(thm)], ['395', '396', '397'])).
% 1.74/1.97  thf('399', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.74/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.74/1.97      inference('sup-', [status(thm)], ['160', '398'])).
% 1.74/1.97  thf('400', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('401', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('402', plain,
% 1.74/1.97      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.74/1.97      inference('demod', [status(thm)], ['399', '400', '401'])).
% 1.74/1.97  thf('403', plain,
% 1.74/1.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X13)
% 1.74/1.97          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 1.74/1.97              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 1.74/1.97          | ~ (v1_relat_1 @ X15)
% 1.74/1.97          | ~ (v1_relat_1 @ X14))),
% 1.74/1.97      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.74/1.97  thf('404', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.74/1.97            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.74/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ~ (v1_relat_1 @ sk_C))),
% 1.74/1.97      inference('sup+', [status(thm)], ['402', '403'])).
% 1.74/1.97  thf('405', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('406', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.74/1.97            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.74/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.74/1.97          | ~ (v1_relat_1 @ X0))),
% 1.74/1.97      inference('demod', [status(thm)], ['404', '405'])).
% 1.74/1.97  thf('407', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ sk_C)
% 1.74/1.97          | ~ (v1_funct_1 @ sk_C)
% 1.74/1.97          | ~ (v1_relat_1 @ X0)
% 1.74/1.97          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.74/1.97              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.74/1.97      inference('sup-', [status(thm)], ['159', '406'])).
% 1.74/1.97  thf('408', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('409', plain, ((v1_funct_1 @ sk_C)),
% 1.74/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.97  thf('410', plain,
% 1.74/1.97      (![X0 : $i]:
% 1.74/1.97         (~ (v1_relat_1 @ X0)
% 1.74/1.97          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.74/1.97              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.74/1.97      inference('demod', [status(thm)], ['407', '408', '409'])).
% 1.74/1.97  thf('411', plain,
% 1.74/1.97      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.74/1.97          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.74/1.97        | ~ (v1_relat_1 @ sk_D))),
% 1.74/1.97      inference('sup+', [status(thm)], ['158', '410'])).
% 1.74/1.97  thf('412', plain,
% 1.74/1.97      (![X21 : $i]:
% 1.74/1.97         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.74/1.97          | ~ (v1_funct_1 @ X21)
% 1.74/1.97          | ~ (v1_relat_1 @ X21))),
% 1.74/1.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.74/1.97  thf('413', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.74/1.97      inference('sup-', [status(thm)], ['143', '144'])).
% 1.74/1.97  thf('414', plain,
% 1.74/1.97      (![X5 : $i, X6 : $i]:
% 1.74/1.97         (~ (v4_relat_1 @ X5 @ X6)
% 1.74/1.97          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.74/1.97          | ~ (v1_relat_1 @ X5))),
% 1.74/1.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.74/1.97  thf('415', plain,
% 1.74/1.97      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.74/1.97      inference('sup-', [status(thm)], ['413', '414'])).
% 1.74/1.97  thf('416', plain, ((v1_relat_1 @ sk_C)),
% 1.74/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.74/1.97  thf('417', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.74/1.97      inference('demod', [status(thm)], ['415', '416'])).
% 1.74/1.97  thf('418', plain,
% 1.74/1.97      (![X28 : $i]:
% 1.74/1.97         (~ (v2_funct_1 @ X28)
% 1.81/1.97          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 1.81/1.97          | ~ (v1_funct_1 @ X28)
% 1.81/1.97          | ~ (v1_relat_1 @ X28))),
% 1.81/1.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.81/1.97  thf('419', plain,
% 1.81/1.97      (![X19 : $i, X20 : $i]:
% 1.81/1.97         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 1.81/1.97          | ((k5_relat_1 @ X19 @ (k6_partfun1 @ X20)) = (X19))
% 1.81/1.97          | ~ (v1_relat_1 @ X19))),
% 1.81/1.97      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/1.97  thf('420', plain,
% 1.81/1.97      (![X0 : $i, X1 : $i]:
% 1.81/1.97         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.81/1.97          | ~ (v1_relat_1 @ X0)
% 1.81/1.97          | ~ (v1_funct_1 @ X0)
% 1.81/1.97          | ~ (v2_funct_1 @ X0)
% 1.81/1.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.81/1.97          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 1.81/1.97              = (k2_funct_1 @ X0)))),
% 1.81/1.97      inference('sup-', [status(thm)], ['418', '419'])).
% 1.81/1.97  thf('421', plain,
% 1.81/1.97      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.81/1.97          = (k2_funct_1 @ sk_C))
% 1.81/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.81/1.97        | ~ (v2_funct_1 @ sk_C)
% 1.81/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.81/1.97        | ~ (v1_relat_1 @ sk_C))),
% 1.81/1.97      inference('sup-', [status(thm)], ['417', '420'])).
% 1.81/1.97  thf('422', plain, ((v2_funct_1 @ sk_C)),
% 1.81/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/1.97  thf('423', plain, ((v1_funct_1 @ sk_C)),
% 1.81/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/1.97  thf('424', plain, ((v1_relat_1 @ sk_C)),
% 1.81/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.81/1.97  thf('425', plain,
% 1.81/1.97      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.81/1.97          = (k2_funct_1 @ sk_C))
% 1.81/1.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.81/1.97      inference('demod', [status(thm)], ['421', '422', '423', '424'])).
% 1.81/1.97  thf('426', plain,
% 1.81/1.97      ((~ (v1_relat_1 @ sk_C)
% 1.81/1.97        | ~ (v1_funct_1 @ sk_C)
% 1.81/1.97        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.81/1.97            = (k2_funct_1 @ sk_C)))),
% 1.81/1.97      inference('sup-', [status(thm)], ['412', '425'])).
% 1.81/1.97  thf('427', plain, ((v1_relat_1 @ sk_C)),
% 1.81/1.97      inference('sup-', [status(thm)], ['58', '59'])).
% 1.81/1.97  thf('428', plain, ((v1_funct_1 @ sk_C)),
% 1.81/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/1.97  thf('429', plain,
% 1.81/1.97      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.81/1.97         = (k2_funct_1 @ sk_C))),
% 1.81/1.97      inference('demod', [status(thm)], ['426', '427', '428'])).
% 1.81/1.97  thf('430', plain, ((v1_relat_1 @ sk_D)),
% 1.81/1.97      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/1.97  thf('431', plain,
% 1.81/1.97      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 1.81/1.97      inference('demod', [status(thm)], ['411', '429', '430'])).
% 1.81/1.97  thf('432', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.81/1.97      inference('sup+', [status(thm)], ['157', '431'])).
% 1.81/1.97  thf('433', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.81/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/1.97  thf('434', plain, ($false),
% 1.81/1.97      inference('simplify_reflect-', [status(thm)], ['432', '433'])).
% 1.81/1.97  
% 1.81/1.97  % SZS output end Refutation
% 1.81/1.97  
% 1.81/1.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
