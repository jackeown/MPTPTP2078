%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yebNIkGnX5

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:18 EST 2020

% Result     : Theorem 2.60s
% Output     : Refutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  459 (21260 expanded)
%              Number of leaves         :   66 (6735 expanded)
%              Depth                    :   53
%              Number of atoms          : 4057 (342407 expanded)
%              Number of equality atoms :  296 (23610 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X21 ) )
      = ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('5',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X21: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X21 ) )
      = ( k6_partfun1 @ X21 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X17 ) @ ( k4_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('11',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X11: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('17',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('33',plain,(
    ! [X11: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X11: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('46',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

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

thf('47',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('49',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_funct_2 @ X63 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ~ ( r2_relset_1 @ X64 @ X64 @ ( k1_partfun1 @ X64 @ X65 @ X65 @ X64 @ X63 @ X66 ) @ ( k6_partfun1 @ X64 ) )
      | ( ( k2_relset_1 @ X65 @ X64 @ X66 )
        = X64 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X65 @ X64 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('69',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('70',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('71',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('76',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('84',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['61','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('92',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('94',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['90','95'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('97',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('98',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ( sk_A
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','57','58','59','60'])).

thf('100',plain,(
    ! [X11: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['99','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('109',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','109'])).

thf('111',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('112',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ sk_A )
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ sk_A )
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['46','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('119',plain,
    ( ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ sk_A )
    = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_A )
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['45','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','57','58','59','60'])).

thf('122',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('123',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_A )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('125',plain,
    ( ( k10_relat_1 @ sk_D @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('127',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['120','125','126'])).

thf('128',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['44','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('130',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('131',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('132',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('133',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['130','133'])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('137',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['13','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('140',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('142',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('145',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('146',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ! [X11: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('148',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X17 ) @ ( k4_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_D ) ) )
        = ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_D ) ) )
        = ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['2','152'])).

thf('154',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','109'])).

thf('155',plain,(
    ! [X21: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X21 ) )
      = ( k6_partfun1 @ X21 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','57','58','59','60'])).

thf('157',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('158',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('160',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('162',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','109'])).

thf('163',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('164',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('165',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('166',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('170',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('171',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('174',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('176',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_funct_1 @ X24 )
        = ( k4_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('180',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','182','183'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('185',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('186',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('192',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','182','183'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('194',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('195',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['192','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('201',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('203',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X11: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('205',plain,
    ( ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['174','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('209',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['173','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('212',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X17 ) @ ( k4_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X11: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['172','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('221',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('222',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('223',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['165','223'])).

thf('225',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
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

thf('227',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X49 @ X50 @ X52 @ X53 @ X48 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('228',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['225','230'])).

thf('232',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('235',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('237',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
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

thf('240',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( ( k1_partfun1 @ X57 @ X58 @ X60 @ X61 @ X56 @ X59 )
        = ( k5_relat_1 @ X56 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('241',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['238','243'])).

thf('245',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['237','246'])).

thf('248',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','247'])).

thf('249',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X17 ) @ ( k4_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('250',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ( X31
        = ( k2_funct_1 @ X32 ) )
      | ( ( k5_relat_1 @ X31 @ X32 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
      | ( ( k2_relat_1 @ X31 )
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('251',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('252',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ( X31
        = ( k2_funct_1 @ X32 ) )
      | ( ( k5_relat_1 @ X31 @ X32 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X32 ) ) )
      | ( ( k2_relat_1 @ X31 )
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X1 ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
       != ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ( ( k4_relat_1 @ X0 )
        = ( k2_funct_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['249','252'])).

thf('254',plain,
    ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
     != ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['248','253'])).

thf('255',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['210','211'])).

thf('256',plain,(
    ! [X11: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('257',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X17 ) @ ( k4_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['255','258'])).

thf('260',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('261',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('262',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['210','211'])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['256','257'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['263','268'])).

thf('270',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['210','211'])).

thf('271',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('272',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('273',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['269','270','271','272'])).

thf('274',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('275',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','57','58','59','60'])).

thf('276',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['210','211'])).

thf('277',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('278',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['210','211'])).

thf('279',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['210','211'])).

thf('281',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('282',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['210','211'])).

thf('283',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('285',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['285','286'])).

thf('288',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('289',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('290',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('291',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['153','154','155','160','161','162','163'])).

thf('293',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('294',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('295',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('296',plain,
    ( ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['254','273','274','275','276','277','278','279','280','281','282','287','288','289','290','291','292','293','294','295'])).

thf('297',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('299',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('301',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('302',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['300','301'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('303',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( X44 = X47 )
      | ~ ( r2_relset_1 @ X45 @ X46 @ X44 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('304',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('305',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['299','304'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('306',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X55 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('307',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['296','307'])).

thf('309',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['308'])).

thf('310',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('311',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('312',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('313',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('314',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_funct_2 @ X71 @ X72 @ X73 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) )
      | ( zip_tseitin_0 @ X71 @ X74 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X75 @ X72 @ X72 @ X73 @ X74 @ X71 ) )
      | ( zip_tseitin_1 @ X73 @ X72 )
      | ( ( k2_relset_1 @ X75 @ X72 @ X74 )
       != X72 )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X72 ) ) )
      | ~ ( v1_funct_2 @ X74 @ X75 @ X72 )
      | ~ ( v1_funct_1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('315',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['315','316','317'])).

thf('319',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['312','318'])).

thf('320',plain,(
    ! [X27: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('321',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('322',plain,(
    ! [X27: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['320','321'])).

thf('323',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['319','322','323','324','325','326'])).

thf('328',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['327'])).

thf('329',plain,(
    ! [X69: $i,X70: $i] :
      ( ( X69 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('330',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['328','329'])).

thf('331',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['330','331'])).

thf('333',plain,(
    ! [X67: $i,X68: $i] :
      ( ( v2_funct_1 @ X68 )
      | ~ ( zip_tseitin_0 @ X68 @ X67 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('334',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['332','333'])).

thf('335',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['309','334'])).

thf('336',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_funct_1 @ X24 )
        = ( k4_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('338',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['336','337'])).

thf('339',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('340',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['338','339'])).

thf('341',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['332','333'])).

thf('342',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['340','341'])).

thf('343',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['335','342'])).

thf('344',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('345',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ( X79 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X80 )
      | ~ ( v1_funct_2 @ X80 @ X81 @ X79 )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X79 ) ) )
      | ( ( k5_relat_1 @ X80 @ ( k2_funct_1 @ X80 ) )
        = ( k6_partfun1 @ X81 ) )
      | ~ ( v2_funct_1 @ X80 )
      | ( ( k2_relset_1 @ X81 @ X79 @ X80 )
       != X79 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('346',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['344','345'])).

thf('347',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('348',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['346','347','348','349'])).

thf('351',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['350','351'])).

thf('353',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['54','57','58','59','60'])).

thf('354',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['352','353'])).

thf('355',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['354'])).

thf('356',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['332','333'])).

thf('357',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['355','356'])).

thf('358',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['340','341'])).

thf('359',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['357','358'])).

thf('360',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('361',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('362',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['360','361'])).

thf('363',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['359','362'])).

thf('364',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('365',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('366',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('367',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('368',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X34 @ X35 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('369',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['367','368'])).

thf('370',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('371',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['369','370'])).

thf('372',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('373',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k8_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k10_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('374',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['372','373'])).

thf('375',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['371','374'])).

thf('376',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['366','375'])).

thf('377',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('378',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['376','377'])).

thf('379',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('380',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['357','358'])).

thf('381',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('382',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('383',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['93','94'])).

thf('384',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['363','364','365','378','379','380','381','382','383'])).

thf('385',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['343','384'])).

thf('386',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['385'])).

thf('387',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['164','386'])).

thf('388',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','182','183'])).

thf('390',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['388','389'])).

thf('391',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['387','390'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yebNIkGnX5
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.60/2.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.60/2.83  % Solved by: fo/fo7.sh
% 2.60/2.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.60/2.83  % done 3052 iterations in 2.378s
% 2.60/2.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.60/2.83  % SZS output start Refutation
% 2.60/2.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.60/2.83  thf(sk_A_type, type, sk_A: $i).
% 2.60/2.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.60/2.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.60/2.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.60/2.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.60/2.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.60/2.83  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.60/2.83  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.60/2.83  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.60/2.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.60/2.83  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.60/2.83  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.60/2.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.60/2.83  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.60/2.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.60/2.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.60/2.83  thf(sk_B_type, type, sk_B: $i).
% 2.60/2.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.60/2.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.60/2.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.60/2.83  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.60/2.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.60/2.83  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.60/2.83  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.60/2.83  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.60/2.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.60/2.83  thf(sk_D_type, type, sk_D: $i).
% 2.60/2.83  thf(sk_C_type, type, sk_C: $i).
% 2.60/2.83  thf(t78_relat_1, axiom,
% 2.60/2.83    (![A:$i]:
% 2.60/2.83     ( ( v1_relat_1 @ A ) =>
% 2.60/2.83       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.60/2.83  thf('0', plain,
% 2.60/2.83      (![X22 : $i]:
% 2.60/2.83         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.60/2.83          | ~ (v1_relat_1 @ X22))),
% 2.60/2.83      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.60/2.83  thf(redefinition_k6_partfun1, axiom,
% 2.60/2.83    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.60/2.83  thf('1', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 2.60/2.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.60/2.83  thf('2', plain,
% 2.60/2.83      (![X22 : $i]:
% 2.60/2.83         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.60/2.83          | ~ (v1_relat_1 @ X22))),
% 2.60/2.83      inference('demod', [status(thm)], ['0', '1'])).
% 2.60/2.83  thf('3', plain,
% 2.60/2.83      (![X22 : $i]:
% 2.60/2.83         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.60/2.83          | ~ (v1_relat_1 @ X22))),
% 2.60/2.83      inference('demod', [status(thm)], ['0', '1'])).
% 2.60/2.83  thf(t72_relat_1, axiom,
% 2.60/2.83    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 2.60/2.83  thf('4', plain,
% 2.60/2.83      (![X21 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X21)) = (k6_relat_1 @ X21))),
% 2.60/2.83      inference('cnf', [status(esa)], [t72_relat_1])).
% 2.60/2.83  thf('5', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 2.60/2.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.60/2.83  thf('6', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 2.60/2.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.60/2.83  thf('7', plain,
% 2.60/2.83      (![X21 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X21)) = (k6_partfun1 @ X21))),
% 2.60/2.83      inference('demod', [status(thm)], ['4', '5', '6'])).
% 2.60/2.83  thf(t54_relat_1, axiom,
% 2.60/2.83    (![A:$i]:
% 2.60/2.83     ( ( v1_relat_1 @ A ) =>
% 2.60/2.83       ( ![B:$i]:
% 2.60/2.83         ( ( v1_relat_1 @ B ) =>
% 2.60/2.83           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.60/2.83             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 2.60/2.83  thf('8', plain,
% 2.60/2.83      (![X17 : $i, X18 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X17)
% 2.60/2.83          | ((k4_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 2.60/2.83              = (k5_relat_1 @ (k4_relat_1 @ X17) @ (k4_relat_1 @ X18)))
% 2.60/2.83          | ~ (v1_relat_1 @ X18))),
% 2.60/2.83      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.60/2.83  thf('9', plain,
% 2.60/2.83      (![X0 : $i, X1 : $i]:
% 2.60/2.83         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.60/2.83            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 2.60/2.83          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.60/2.83          | ~ (v1_relat_1 @ X1))),
% 2.60/2.83      inference('sup+', [status(thm)], ['7', '8'])).
% 2.60/2.83  thf(fc4_funct_1, axiom,
% 2.60/2.83    (![A:$i]:
% 2.60/2.83     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.60/2.83       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.60/2.83  thf('10', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.60/2.83      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.60/2.83  thf('11', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 2.60/2.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.60/2.83  thf('12', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.60/2.83      inference('demod', [status(thm)], ['10', '11'])).
% 2.60/2.83  thf('13', plain,
% 2.60/2.83      (![X0 : $i, X1 : $i]:
% 2.60/2.83         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.60/2.83            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 2.60/2.83          | ~ (v1_relat_1 @ X1))),
% 2.60/2.83      inference('demod', [status(thm)], ['9', '12'])).
% 2.60/2.83  thf(dt_k4_relat_1, axiom,
% 2.60/2.83    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 2.60/2.83  thf('14', plain,
% 2.60/2.83      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.83      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.83  thf(t37_relat_1, axiom,
% 2.60/2.83    (![A:$i]:
% 2.60/2.83     ( ( v1_relat_1 @ A ) =>
% 2.60/2.83       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 2.60/2.83         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 2.60/2.83  thf('15', plain,
% 2.60/2.83      (![X14 : $i]:
% 2.60/2.83         (((k1_relat_1 @ X14) = (k2_relat_1 @ (k4_relat_1 @ X14)))
% 2.60/2.83          | ~ (v1_relat_1 @ X14))),
% 2.60/2.83      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.60/2.83  thf(involutiveness_k4_relat_1, axiom,
% 2.60/2.83    (![A:$i]:
% 2.60/2.83     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 2.60/2.83  thf('16', plain,
% 2.60/2.83      (![X11 : $i]:
% 2.60/2.83         (((k4_relat_1 @ (k4_relat_1 @ X11)) = (X11)) | ~ (v1_relat_1 @ X11))),
% 2.60/2.83      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.60/2.83  thf('17', plain,
% 2.60/2.83      (![X14 : $i]:
% 2.60/2.83         (((k2_relat_1 @ X14) = (k1_relat_1 @ (k4_relat_1 @ X14)))
% 2.60/2.83          | ~ (v1_relat_1 @ X14))),
% 2.60/2.83      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.60/2.83  thf(t146_relat_1, axiom,
% 2.60/2.83    (![A:$i]:
% 2.60/2.83     ( ( v1_relat_1 @ A ) =>
% 2.60/2.83       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.60/2.83  thf('18', plain,
% 2.60/2.83      (![X12 : $i]:
% 2.60/2.83         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 2.60/2.83          | ~ (v1_relat_1 @ X12))),
% 2.60/2.83      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.60/2.83  thf('19', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (((k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.60/2.83            = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83          | ~ (v1_relat_1 @ X0)
% 2.60/2.83          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.83      inference('sup+', [status(thm)], ['17', '18'])).
% 2.60/2.83  thf('20', plain,
% 2.60/2.83      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.83      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.83  thf('21', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k9_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.60/2.83              = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 2.60/2.83      inference('clc', [status(thm)], ['19', '20'])).
% 2.60/2.83  thf('22', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83            = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.60/2.83          | ~ (v1_relat_1 @ X0)
% 2.60/2.83          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.83      inference('sup+', [status(thm)], ['16', '21'])).
% 2.60/2.83  thf('23', plain,
% 2.60/2.83      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.83      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.83  thf('24', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.83      inference('clc', [status(thm)], ['22', '23'])).
% 2.60/2.83  thf('25', plain,
% 2.60/2.83      (![X14 : $i]:
% 2.60/2.83         (((k1_relat_1 @ X14) = (k2_relat_1 @ (k4_relat_1 @ X14)))
% 2.60/2.83          | ~ (v1_relat_1 @ X14))),
% 2.60/2.83      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.60/2.83  thf('26', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.83            = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 2.60/2.83          | ~ (v1_relat_1 @ X0)
% 2.60/2.83          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.83      inference('sup+', [status(thm)], ['24', '25'])).
% 2.60/2.83  thf('27', plain,
% 2.60/2.83      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.83      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.83  thf('28', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.83              = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.83      inference('clc', [status(thm)], ['26', '27'])).
% 2.60/2.83  thf('29', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.83            = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.60/2.83          | ~ (v1_relat_1 @ X0)
% 2.60/2.83          | ~ (v1_relat_1 @ X0))),
% 2.60/2.83      inference('sup+', [status(thm)], ['15', '28'])).
% 2.60/2.83  thf('30', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.83              = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 2.60/2.83      inference('simplify', [status(thm)], ['29'])).
% 2.60/2.83  thf('31', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.83              = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.83      inference('clc', [status(thm)], ['26', '27'])).
% 2.60/2.83  thf('32', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.83      inference('clc', [status(thm)], ['22', '23'])).
% 2.60/2.83  thf('33', plain,
% 2.60/2.83      (![X11 : $i]:
% 2.60/2.83         (((k4_relat_1 @ (k4_relat_1 @ X11)) = (X11)) | ~ (v1_relat_1 @ X11))),
% 2.60/2.83      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.60/2.83  thf('34', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.83      inference('clc', [status(thm)], ['22', '23'])).
% 2.60/2.83  thf('35', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83            = (k2_relat_1 @ X0))
% 2.60/2.83          | ~ (v1_relat_1 @ X0)
% 2.60/2.83          | ~ (v1_relat_1 @ X0))),
% 2.60/2.83      inference('sup+', [status(thm)], ['33', '34'])).
% 2.60/2.83  thf('36', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83              = (k2_relat_1 @ X0)))),
% 2.60/2.83      inference('simplify', [status(thm)], ['35'])).
% 2.60/2.83  thf('37', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (((k9_relat_1 @ (k4_relat_1 @ X0) @ 
% 2.60/2.83            (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 2.60/2.83            = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83          | ~ (v1_relat_1 @ X0)
% 2.60/2.83          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.83      inference('sup+', [status(thm)], ['32', '36'])).
% 2.60/2.83  thf('38', plain,
% 2.60/2.83      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.83      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.83  thf('39', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k9_relat_1 @ (k4_relat_1 @ X0) @ 
% 2.60/2.83              (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 2.60/2.83              = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 2.60/2.83      inference('clc', [status(thm)], ['37', '38'])).
% 2.60/2.83  thf('40', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (((k9_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83            = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83          | ~ (v1_relat_1 @ X0)
% 2.60/2.83          | ~ (v1_relat_1 @ X0))),
% 2.60/2.83      inference('sup+', [status(thm)], ['31', '39'])).
% 2.60/2.83  thf('41', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k9_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83              = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 2.60/2.83      inference('simplify', [status(thm)], ['40'])).
% 2.60/2.83  thf('42', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83            = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.83          | ~ (v1_relat_1 @ X0))),
% 2.60/2.83      inference('sup+', [status(thm)], ['30', '41'])).
% 2.60/2.83  thf('43', plain,
% 2.60/2.83      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.83      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.83  thf('44', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_relat_1 @ X0)
% 2.60/2.83          | ((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.83              = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 2.60/2.83      inference('clc', [status(thm)], ['42', '43'])).
% 2.60/2.83  thf('45', plain,
% 2.60/2.83      (![X11 : $i]:
% 2.60/2.83         (((k4_relat_1 @ (k4_relat_1 @ X11)) = (X11)) | ~ (v1_relat_1 @ X11))),
% 2.60/2.83      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.60/2.83  thf('46', plain,
% 2.60/2.83      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.83      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.83  thf(t36_funct_2, conjecture,
% 2.60/2.83    (![A:$i,B:$i,C:$i]:
% 2.60/2.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.60/2.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.60/2.83       ( ![D:$i]:
% 2.60/2.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.60/2.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.60/2.83           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.60/2.83               ( r2_relset_1 @
% 2.60/2.83                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.60/2.83                 ( k6_partfun1 @ A ) ) & 
% 2.60/2.83               ( v2_funct_1 @ C ) ) =>
% 2.60/2.83             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.60/2.83               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.60/2.83  thf(zf_stmt_0, negated_conjecture,
% 2.60/2.83    (~( ![A:$i,B:$i,C:$i]:
% 2.60/2.83        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.60/2.83            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.60/2.83          ( ![D:$i]:
% 2.60/2.83            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.60/2.83                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.60/2.83              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.60/2.83                  ( r2_relset_1 @
% 2.60/2.83                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.60/2.83                    ( k6_partfun1 @ A ) ) & 
% 2.60/2.83                  ( v2_funct_1 @ C ) ) =>
% 2.60/2.83                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.60/2.83                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.60/2.83    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.60/2.83  thf('47', plain,
% 2.60/2.83      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.60/2.83        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.60/2.83        (k6_partfun1 @ sk_A))),
% 2.60/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.83  thf('48', plain,
% 2.60/2.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.60/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.83  thf(t24_funct_2, axiom,
% 2.60/2.83    (![A:$i,B:$i,C:$i]:
% 2.60/2.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.60/2.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.60/2.83       ( ![D:$i]:
% 2.60/2.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.60/2.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.60/2.83           ( ( r2_relset_1 @
% 2.60/2.83               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.60/2.83               ( k6_partfun1 @ B ) ) =>
% 2.60/2.83             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.60/2.83  thf('49', plain,
% 2.60/2.83      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 2.60/2.83         (~ (v1_funct_1 @ X63)
% 2.60/2.83          | ~ (v1_funct_2 @ X63 @ X64 @ X65)
% 2.60/2.83          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 2.60/2.83          | ~ (r2_relset_1 @ X64 @ X64 @ 
% 2.60/2.83               (k1_partfun1 @ X64 @ X65 @ X65 @ X64 @ X63 @ X66) @ 
% 2.60/2.83               (k6_partfun1 @ X64))
% 2.60/2.83          | ((k2_relset_1 @ X65 @ X64 @ X66) = (X64))
% 2.60/2.83          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64)))
% 2.60/2.83          | ~ (v1_funct_2 @ X66 @ X65 @ X64)
% 2.60/2.83          | ~ (v1_funct_1 @ X66))),
% 2.60/2.83      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.60/2.83  thf('50', plain,
% 2.60/2.83      (![X0 : $i]:
% 2.60/2.83         (~ (v1_funct_1 @ X0)
% 2.60/2.83          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.60/2.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.60/2.83          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.60/2.83          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.60/2.83               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.60/2.83               (k6_partfun1 @ sk_A))
% 2.60/2.83          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.60/2.83          | ~ (v1_funct_1 @ sk_C))),
% 2.60/2.83      inference('sup-', [status(thm)], ['48', '49'])).
% 2.60/2.83  thf('51', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.60/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.83  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 2.60/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('53', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_funct_1 @ X0)
% 2.60/2.84          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.60/2.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.60/2.84          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.60/2.84          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.60/2.84               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.60/2.84               (k6_partfun1 @ sk_A)))),
% 2.60/2.84      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.60/2.84  thf('54', plain,
% 2.60/2.84      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.60/2.84        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.60/2.84        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.60/2.84        | ~ (v1_funct_1 @ sk_D))),
% 2.60/2.84      inference('sup-', [status(thm)], ['47', '53'])).
% 2.60/2.84  thf('55', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(redefinition_k2_relset_1, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i]:
% 2.60/2.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.60/2.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.60/2.84  thf('56', plain,
% 2.60/2.84      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.60/2.84         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 2.60/2.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.60/2.84  thf('57', plain,
% 2.60/2.84      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup-', [status(thm)], ['55', '56'])).
% 2.60/2.84  thf('58', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('61', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['54', '57', '58', '59', '60'])).
% 2.60/2.84  thf('62', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.84              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.84      inference('clc', [status(thm)], ['22', '23'])).
% 2.60/2.84  thf('63', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.84              = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.84      inference('clc', [status(thm)], ['26', '27'])).
% 2.60/2.84  thf('64', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (((k1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.84            = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ X0))),
% 2.60/2.84      inference('sup+', [status(thm)], ['62', '63'])).
% 2.60/2.84  thf('65', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.84              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.84      inference('simplify', [status(thm)], ['64'])).
% 2.60/2.84  thf('66', plain,
% 2.60/2.84      (![X14 : $i]:
% 2.60/2.84         (((k2_relat_1 @ X14) = (k1_relat_1 @ (k4_relat_1 @ X14)))
% 2.60/2.84          | ~ (v1_relat_1 @ X14))),
% 2.60/2.84      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.60/2.84  thf('67', plain,
% 2.60/2.84      (![X22 : $i]:
% 2.60/2.84         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.60/2.84          | ~ (v1_relat_1 @ X22))),
% 2.60/2.84      inference('demod', [status(thm)], ['0', '1'])).
% 2.60/2.84  thf('68', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.60/2.84            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 2.60/2.84          | ~ (v1_relat_1 @ X1))),
% 2.60/2.84      inference('demod', [status(thm)], ['9', '12'])).
% 2.60/2.84  thf(t71_relat_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.60/2.84       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.60/2.84  thf('69', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 2.60/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.60/2.84  thf('70', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.60/2.84  thf('71', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 2.60/2.84      inference('demod', [status(thm)], ['69', '70'])).
% 2.60/2.84  thf(t45_relat_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( v1_relat_1 @ A ) =>
% 2.60/2.84       ( ![B:$i]:
% 2.60/2.84         ( ( v1_relat_1 @ B ) =>
% 2.60/2.84           ( r1_tarski @
% 2.60/2.84             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.60/2.84  thf('72', plain,
% 2.60/2.84      (![X15 : $i, X16 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X15)
% 2.60/2.84          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X16 @ X15)) @ 
% 2.60/2.84             (k2_relat_1 @ X15))
% 2.60/2.84          | ~ (v1_relat_1 @ X16))),
% 2.60/2.84      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.60/2.84  thf('73', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0))) @ 
% 2.60/2.84           X0)
% 2.60/2.84          | ~ (v1_relat_1 @ X1)
% 2.60/2.84          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['71', '72'])).
% 2.60/2.84  thf('74', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.60/2.84      inference('demod', [status(thm)], ['10', '11'])).
% 2.60/2.84  thf('75', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0))) @ 
% 2.60/2.84           X0)
% 2.60/2.84          | ~ (v1_relat_1 @ X1))),
% 2.60/2.84      inference('demod', [status(thm)], ['73', '74'])).
% 2.60/2.84  thf(t3_subset, axiom,
% 2.60/2.84    (![A:$i,B:$i]:
% 2.60/2.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.60/2.84  thf('76', plain,
% 2.60/2.84      (![X3 : $i, X5 : $i]:
% 2.60/2.84         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 2.60/2.84      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.84  thf('77', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X1)
% 2.60/2.84          | (m1_subset_1 @ 
% 2.60/2.84             (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0))) @ 
% 2.60/2.84             (k1_zfmisc_1 @ X0)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['75', '76'])).
% 2.60/2.84  thf('78', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         ((m1_subset_1 @ 
% 2.60/2.84           (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))) @ 
% 2.60/2.84           (k1_zfmisc_1 @ X1))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['68', '77'])).
% 2.60/2.84  thf('79', plain,
% 2.60/2.84      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.84  thf('80', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | (m1_subset_1 @ 
% 2.60/2.84             (k2_relat_1 @ 
% 2.60/2.84              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))) @ 
% 2.60/2.84             (k1_zfmisc_1 @ X1)))),
% 2.60/2.84      inference('clc', [status(thm)], ['78', '79'])).
% 2.60/2.84  thf('81', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         ((m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ 
% 2.60/2.84           (k1_zfmisc_1 @ (k1_relat_1 @ X0)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ X0))),
% 2.60/2.84      inference('sup+', [status(thm)], ['67', '80'])).
% 2.60/2.84  thf('82', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | (m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ 
% 2.60/2.84             (k1_zfmisc_1 @ (k1_relat_1 @ X0))))),
% 2.60/2.84      inference('simplify', [status(thm)], ['81'])).
% 2.60/2.84  thf('83', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         ((m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 2.60/2.84           (k1_zfmisc_1 @ (k2_relat_1 @ X0)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['66', '82'])).
% 2.60/2.84  thf('84', plain,
% 2.60/2.84      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.84  thf('85', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | (m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 2.60/2.84             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 2.60/2.84      inference('clc', [status(thm)], ['83', '84'])).
% 2.60/2.84  thf('86', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         ((m1_subset_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ 
% 2.60/2.84           (k1_zfmisc_1 @ (k2_relat_1 @ X0)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ X0))),
% 2.60/2.84      inference('sup+', [status(thm)], ['65', '85'])).
% 2.60/2.84  thf('87', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | (m1_subset_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ 
% 2.60/2.84             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 2.60/2.84      inference('simplify', [status(thm)], ['86'])).
% 2.60/2.84  thf('88', plain,
% 2.60/2.84      (![X3 : $i, X4 : $i]:
% 2.60/2.84         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 2.60/2.84      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.84  thf('89', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['87', '88'])).
% 2.60/2.84  thf('90', plain,
% 2.60/2.84      (((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ sk_D)) @ sk_A)
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup+', [status(thm)], ['61', '89'])).
% 2.60/2.84  thf('91', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(cc2_relat_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( v1_relat_1 @ A ) =>
% 2.60/2.84       ( ![B:$i]:
% 2.60/2.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.60/2.84  thf('92', plain,
% 2.60/2.84      (![X6 : $i, X7 : $i]:
% 2.60/2.84         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 2.60/2.84          | (v1_relat_1 @ X6)
% 2.60/2.84          | ~ (v1_relat_1 @ X7))),
% 2.60/2.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.60/2.84  thf('93', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup-', [status(thm)], ['91', '92'])).
% 2.60/2.84  thf(fc6_relat_1, axiom,
% 2.60/2.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.60/2.84  thf('94', plain,
% 2.60/2.84      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 2.60/2.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.60/2.84  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('96', plain, ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ sk_D)) @ sk_A)),
% 2.60/2.84      inference('demod', [status(thm)], ['90', '95'])).
% 2.60/2.84  thf(d10_xboole_0, axiom,
% 2.60/2.84    (![A:$i,B:$i]:
% 2.60/2.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.60/2.84  thf('97', plain,
% 2.60/2.84      (![X0 : $i, X2 : $i]:
% 2.60/2.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.60/2.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.60/2.84  thf('98', plain,
% 2.60/2.84      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_D)))
% 2.60/2.84        | ((sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_D))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['96', '97'])).
% 2.60/2.84  thf('99', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['54', '57', '58', '59', '60'])).
% 2.60/2.84  thf('100', plain,
% 2.60/2.84      (![X11 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k4_relat_1 @ X11)) = (X11)) | ~ (v1_relat_1 @ X11))),
% 2.60/2.84      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.60/2.84  thf('101', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | (m1_subset_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ 
% 2.60/2.84             (k1_zfmisc_1 @ (k1_relat_1 @ X0))))),
% 2.60/2.84      inference('simplify', [status(thm)], ['81'])).
% 2.60/2.84  thf('102', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         ((m1_subset_1 @ (k2_relat_1 @ X0) @ 
% 2.60/2.84           (k1_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['100', '101'])).
% 2.60/2.84  thf('103', plain,
% 2.60/2.84      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.84  thf('104', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | (m1_subset_1 @ (k2_relat_1 @ X0) @ 
% 2.60/2.84             (k1_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))))),
% 2.60/2.84      inference('clc', [status(thm)], ['102', '103'])).
% 2.60/2.84  thf('105', plain,
% 2.60/2.84      (![X3 : $i, X4 : $i]:
% 2.60/2.84         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 2.60/2.84      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.84  thf('106', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['104', '105'])).
% 2.60/2.84  thf('107', plain,
% 2.60/2.84      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_D)))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup+', [status(thm)], ['99', '106'])).
% 2.60/2.84  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('109', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['107', '108'])).
% 2.60/2.84  thf('110', plain, (((sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['98', '109'])).
% 2.60/2.84  thf('111', plain,
% 2.60/2.84      (![X14 : $i]:
% 2.60/2.84         (((k1_relat_1 @ X14) = (k2_relat_1 @ (k4_relat_1 @ X14)))
% 2.60/2.84          | ~ (v1_relat_1 @ X14))),
% 2.60/2.84      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.60/2.84  thf(t169_relat_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( v1_relat_1 @ A ) =>
% 2.60/2.84       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.60/2.84  thf('112', plain,
% 2.60/2.84      (![X13 : $i]:
% 2.60/2.84         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 2.60/2.84          | ~ (v1_relat_1 @ X13))),
% 2.60/2.84      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.60/2.84  thf('113', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.60/2.84            = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['111', '112'])).
% 2.60/2.84  thf('114', plain,
% 2.60/2.84      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.84  thf('115', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.60/2.84              = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 2.60/2.84      inference('clc', [status(thm)], ['113', '114'])).
% 2.60/2.84  thf('116', plain,
% 2.60/2.84      ((((k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)) @ sk_A)
% 2.60/2.84          = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['110', '115'])).
% 2.60/2.84  thf('117', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ sk_D)
% 2.60/2.84        | ((k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)) @ sk_A)
% 2.60/2.84            = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['46', '116'])).
% 2.60/2.84  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('119', plain,
% 2.60/2.84      (((k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)) @ sk_A)
% 2.60/2.84         = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))),
% 2.60/2.84      inference('demod', [status(thm)], ['117', '118'])).
% 2.60/2.84  thf('120', plain,
% 2.60/2.84      ((((k10_relat_1 @ sk_D @ sk_A)
% 2.60/2.84          = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup+', [status(thm)], ['45', '119'])).
% 2.60/2.84  thf('121', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['54', '57', '58', '59', '60'])).
% 2.60/2.84  thf('122', plain,
% 2.60/2.84      (![X13 : $i]:
% 2.60/2.84         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 2.60/2.84          | ~ (v1_relat_1 @ X13))),
% 2.60/2.84      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.60/2.84  thf('123', plain,
% 2.60/2.84      ((((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup+', [status(thm)], ['121', '122'])).
% 2.60/2.84  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('125', plain, (((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['123', '124'])).
% 2.60/2.84  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('127', plain,
% 2.60/2.84      (((k1_relat_1 @ sk_D) = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))),
% 2.60/2.84      inference('demod', [status(thm)], ['120', '125', '126'])).
% 2.60/2.84  thf('128', plain,
% 2.60/2.84      ((((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup+', [status(thm)], ['44', '127'])).
% 2.60/2.84  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('130', plain,
% 2.60/2.84      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['128', '129'])).
% 2.60/2.84  thf(t80_relat_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( v1_relat_1 @ A ) =>
% 2.60/2.84       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.60/2.84  thf('131', plain,
% 2.60/2.84      (![X23 : $i]:
% 2.60/2.84         (((k5_relat_1 @ X23 @ (k6_relat_1 @ (k2_relat_1 @ X23))) = (X23))
% 2.60/2.84          | ~ (v1_relat_1 @ X23))),
% 2.60/2.84      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.60/2.84  thf('132', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.60/2.84  thf('133', plain,
% 2.60/2.84      (![X23 : $i]:
% 2.60/2.84         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 2.60/2.84          | ~ (v1_relat_1 @ X23))),
% 2.60/2.84      inference('demod', [status(thm)], ['131', '132'])).
% 2.60/2.84  thf('134', plain,
% 2.60/2.84      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 2.60/2.84          (k6_partfun1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['130', '133'])).
% 2.60/2.84  thf('135', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ sk_D)
% 2.60/2.84        | ((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 2.60/2.84            (k6_partfun1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['14', '134'])).
% 2.60/2.84  thf('136', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('137', plain,
% 2.60/2.84      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 2.60/2.84         = (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['135', '136'])).
% 2.60/2.84  thf('138', plain,
% 2.60/2.84      ((((k4_relat_1 @ 
% 2.60/2.84          (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 2.60/2.84          = (k4_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup+', [status(thm)], ['13', '137'])).
% 2.60/2.84  thf('139', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('140', plain,
% 2.60/2.84      (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 2.60/2.84         = (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['138', '139'])).
% 2.60/2.84  thf('141', plain,
% 2.60/2.84      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.84  thf('142', plain,
% 2.60/2.84      (((v1_relat_1 @ (k4_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v1_relat_1 @ 
% 2.60/2.84             (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['140', '141'])).
% 2.60/2.84  thf('143', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ sk_D)
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D)
% 2.60/2.84        | (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['3', '142'])).
% 2.60/2.84  thf('144', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('145', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('146', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['143', '144', '145'])).
% 2.60/2.84  thf('147', plain,
% 2.60/2.84      (![X11 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k4_relat_1 @ X11)) = (X11)) | ~ (v1_relat_1 @ X11))),
% 2.60/2.84      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.60/2.84  thf('148', plain,
% 2.60/2.84      (![X17 : $i, X18 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X17)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ X17) @ (k4_relat_1 @ X18)))
% 2.60/2.84          | ~ (v1_relat_1 @ X18))),
% 2.60/2.84      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.60/2.84  thf('149', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 2.60/2.84            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ X1)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['147', '148'])).
% 2.60/2.84  thf('150', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ sk_D)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_D)))
% 2.60/2.84              = (k5_relat_1 @ sk_D @ (k4_relat_1 @ X0))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['146', '149'])).
% 2.60/2.84  thf('151', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('152', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_D)))
% 2.60/2.84              = (k5_relat_1 @ sk_D @ (k4_relat_1 @ X0))))),
% 2.60/2.84      inference('demod', [status(thm)], ['150', '151'])).
% 2.60/2.84  thf('153', plain,
% 2.60/2.84      ((((k4_relat_1 @ (k4_relat_1 @ sk_D))
% 2.60/2.84          = (k5_relat_1 @ sk_D @ 
% 2.60/2.84             (k4_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k4_relat_1 @ sk_D))))))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k4_relat_1 @ sk_D)))))),
% 2.60/2.84      inference('sup+', [status(thm)], ['2', '152'])).
% 2.60/2.84  thf('154', plain, (((sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['98', '109'])).
% 2.60/2.84  thf('155', plain,
% 2.60/2.84      (![X21 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X21)) = (k6_partfun1 @ X21))),
% 2.60/2.84      inference('demod', [status(thm)], ['4', '5', '6'])).
% 2.60/2.84  thf('156', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['54', '57', '58', '59', '60'])).
% 2.60/2.84  thf('157', plain,
% 2.60/2.84      (![X23 : $i]:
% 2.60/2.84         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 2.60/2.84          | ~ (v1_relat_1 @ X23))),
% 2.60/2.84      inference('demod', [status(thm)], ['131', '132'])).
% 2.60/2.84  thf('158', plain,
% 2.60/2.84      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup+', [status(thm)], ['156', '157'])).
% 2.60/2.84  thf('159', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('160', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['158', '159'])).
% 2.60/2.84  thf('161', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['143', '144', '145'])).
% 2.60/2.84  thf('162', plain, (((sk_A) = (k1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['98', '109'])).
% 2.60/2.84  thf('163', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 2.60/2.84      inference('demod', [status(thm)], ['10', '11'])).
% 2.60/2.84  thf('164', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('165', plain,
% 2.60/2.84      (![X8 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X8)) | ~ (v1_relat_1 @ X8))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.60/2.84  thf('166', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('167', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 2.60/2.84            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ X1)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['147', '148'])).
% 2.60/2.84  thf('168', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ sk_D)
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 2.60/2.84          | ((k4_relat_1 @ 
% 2.60/2.84              (k5_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ X0))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['166', '167'])).
% 2.60/2.84  thf('169', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('170', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['143', '144', '145'])).
% 2.60/2.84  thf('171', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('172', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ sk_D))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ X0))))),
% 2.60/2.84      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 2.60/2.84  thf('173', plain,
% 2.60/2.84      (![X22 : $i]:
% 2.60/2.84         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.60/2.84          | ~ (v1_relat_1 @ X22))),
% 2.60/2.84      inference('demod', [status(thm)], ['0', '1'])).
% 2.60/2.84  thf('174', plain,
% 2.60/2.84      (![X22 : $i]:
% 2.60/2.84         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 2.60/2.84          | ~ (v1_relat_1 @ X22))),
% 2.60/2.84      inference('demod', [status(thm)], ['0', '1'])).
% 2.60/2.84  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(d9_funct_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.60/2.84       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.60/2.84  thf('176', plain,
% 2.60/2.84      (![X24 : $i]:
% 2.60/2.84         (~ (v2_funct_1 @ X24)
% 2.60/2.84          | ((k2_funct_1 @ X24) = (k4_relat_1 @ X24))
% 2.60/2.84          | ~ (v1_funct_1 @ X24)
% 2.60/2.84          | ~ (v1_relat_1 @ X24))),
% 2.60/2.84      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.60/2.84  thf('177', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ sk_C)
% 2.60/2.84        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_C))),
% 2.60/2.84      inference('sup-', [status(thm)], ['175', '176'])).
% 2.60/2.84  thf('178', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('179', plain,
% 2.60/2.84      (![X6 : $i, X7 : $i]:
% 2.60/2.84         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 2.60/2.84          | (v1_relat_1 @ X6)
% 2.60/2.84          | ~ (v1_relat_1 @ X7))),
% 2.60/2.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.60/2.84  thf('180', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.60/2.84      inference('sup-', [status(thm)], ['178', '179'])).
% 2.60/2.84  thf('181', plain,
% 2.60/2.84      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 2.60/2.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.60/2.84  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('184', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['177', '182', '183'])).
% 2.60/2.84  thf(t55_funct_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.60/2.84       ( ( v2_funct_1 @ A ) =>
% 2.60/2.84         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.60/2.84           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.60/2.84  thf('185', plain,
% 2.60/2.84      (![X30 : $i]:
% 2.60/2.84         (~ (v2_funct_1 @ X30)
% 2.60/2.84          | ((k1_relat_1 @ X30) = (k2_relat_1 @ (k2_funct_1 @ X30)))
% 2.60/2.84          | ~ (v1_funct_1 @ X30)
% 2.60/2.84          | ~ (v1_relat_1 @ X30))),
% 2.60/2.84      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.60/2.84  thf('186', plain,
% 2.60/2.84      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_C)
% 2.60/2.84        | ~ (v1_funct_1 @ sk_C)
% 2.60/2.84        | ~ (v2_funct_1 @ sk_C))),
% 2.60/2.84      inference('sup+', [status(thm)], ['184', '185'])).
% 2.60/2.84  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('190', plain,
% 2.60/2.84      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.60/2.84      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 2.60/2.84  thf('191', plain,
% 2.60/2.84      (![X23 : $i]:
% 2.60/2.84         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 2.60/2.84          | ~ (v1_relat_1 @ X23))),
% 2.60/2.84      inference('demod', [status(thm)], ['131', '132'])).
% 2.60/2.84  thf('192', plain,
% 2.60/2.84      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 2.60/2.84          (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k4_relat_1 @ sk_C))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['190', '191'])).
% 2.60/2.84  thf('193', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['177', '182', '183'])).
% 2.60/2.84  thf(dt_k2_funct_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.60/2.84       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.60/2.84         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.60/2.84  thf('194', plain,
% 2.60/2.84      (![X25 : $i]:
% 2.60/2.84         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 2.60/2.84          | ~ (v1_funct_1 @ X25)
% 2.60/2.84          | ~ (v1_relat_1 @ X25))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.60/2.84  thf('195', plain,
% 2.60/2.84      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_C)
% 2.60/2.84        | ~ (v1_funct_1 @ sk_C))),
% 2.60/2.84      inference('sup+', [status(thm)], ['193', '194'])).
% 2.60/2.84  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('198', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['195', '196', '197'])).
% 2.60/2.84  thf('199', plain,
% 2.60/2.84      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 2.60/2.84         = (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['192', '198'])).
% 2.60/2.84  thf('200', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.60/2.84            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 2.60/2.84          | ~ (v1_relat_1 @ X1))),
% 2.60/2.84      inference('demod', [status(thm)], ['9', '12'])).
% 2.60/2.84  thf('201', plain,
% 2.60/2.84      ((((k4_relat_1 @ 
% 2.60/2.84          (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 2.60/2.84          = (k4_relat_1 @ sk_C))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_C))),
% 2.60/2.84      inference('sup+', [status(thm)], ['199', '200'])).
% 2.60/2.84  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('203', plain,
% 2.60/2.84      (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 2.60/2.84         = (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['201', '202'])).
% 2.60/2.84  thf('204', plain,
% 2.60/2.84      (![X11 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k4_relat_1 @ X11)) = (X11)) | ~ (v1_relat_1 @ X11))),
% 2.60/2.84      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.60/2.84  thf('205', plain,
% 2.60/2.84      ((((k4_relat_1 @ (k4_relat_1 @ sk_C))
% 2.60/2.84          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 2.60/2.84        | ~ (v1_relat_1 @ 
% 2.60/2.84             (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['203', '204'])).
% 2.60/2.84  thf('206', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ sk_C)
% 2.60/2.84        | ~ (v1_relat_1 @ sk_C)
% 2.60/2.84        | ((k4_relat_1 @ (k4_relat_1 @ sk_C))
% 2.60/2.84            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['174', '205'])).
% 2.60/2.84  thf('207', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('209', plain,
% 2.60/2.84      (((k4_relat_1 @ (k4_relat_1 @ sk_C))
% 2.60/2.84         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['206', '207', '208'])).
% 2.60/2.84  thf('210', plain,
% 2.60/2.84      ((((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 2.60/2.84      inference('sup+', [status(thm)], ['173', '209'])).
% 2.60/2.84  thf('211', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('212', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['210', '211'])).
% 2.60/2.84  thf('213', plain,
% 2.60/2.84      (![X17 : $i, X18 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X17)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ X17) @ (k4_relat_1 @ X18)))
% 2.60/2.84          | ~ (v1_relat_1 @ X18))),
% 2.60/2.84      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.60/2.84  thf('214', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 2.60/2.84            = (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['212', '213'])).
% 2.60/2.84  thf('215', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['195', '196', '197'])).
% 2.60/2.84  thf('216', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 2.60/2.84            = (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0))),
% 2.60/2.84      inference('demod', [status(thm)], ['214', '215'])).
% 2.60/2.84  thf('217', plain,
% 2.60/2.84      (![X11 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k4_relat_1 @ X11)) = (X11)) | ~ (v1_relat_1 @ X11))),
% 2.60/2.84      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.60/2.84  thf('218', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 2.60/2.84            = (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C))))),
% 2.60/2.84      inference('sup+', [status(thm)], ['216', '217'])).
% 2.60/2.84  thf('219', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_C)
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 2.60/2.84        | ((k4_relat_1 @ 
% 2.60/2.84            (k5_relat_1 @ sk_C @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 2.60/2.84            = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['172', '218'])).
% 2.60/2.84  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('221', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['143', '144', '145'])).
% 2.60/2.84  thf('222', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('223', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 2.60/2.84        | ((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.60/2.84            = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C))))),
% 2.60/2.84      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 2.60/2.84  thf('224', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.60/2.84        | ((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.60/2.84            = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['165', '223'])).
% 2.60/2.84  thf('225', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('226', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(dt_k1_partfun1, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.60/2.84     ( ( ( v1_funct_1 @ E ) & 
% 2.60/2.84         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.60/2.84         ( v1_funct_1 @ F ) & 
% 2.60/2.84         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.60/2.84       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.60/2.84         ( m1_subset_1 @
% 2.60/2.84           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.60/2.84           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.60/2.84  thf('227', plain,
% 2.60/2.84      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 2.60/2.84         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 2.60/2.84          | ~ (v1_funct_1 @ X48)
% 2.60/2.84          | ~ (v1_funct_1 @ X51)
% 2.60/2.84          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 2.60/2.84          | (m1_subset_1 @ (k1_partfun1 @ X49 @ X50 @ X52 @ X53 @ X48 @ X51) @ 
% 2.60/2.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X53))))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.60/2.84  thf('228', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.84         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.60/2.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.60/2.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.60/2.84          | ~ (v1_funct_1 @ X1)
% 2.60/2.84          | ~ (v1_funct_1 @ sk_C))),
% 2.60/2.84      inference('sup-', [status(thm)], ['226', '227'])).
% 2.60/2.84  thf('229', plain, ((v1_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('230', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.84         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.60/2.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.60/2.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.60/2.84          | ~ (v1_funct_1 @ X1))),
% 2.60/2.84      inference('demod', [status(thm)], ['228', '229'])).
% 2.60/2.84  thf('231', plain,
% 2.60/2.84      ((~ (v1_funct_1 @ sk_D)
% 2.60/2.84        | (m1_subset_1 @ 
% 2.60/2.84           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.60/2.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['225', '230'])).
% 2.60/2.84  thf('232', plain, ((v1_funct_1 @ sk_D)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('233', plain,
% 2.60/2.84      ((m1_subset_1 @ 
% 2.60/2.84        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.60/2.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.60/2.84      inference('demod', [status(thm)], ['231', '232'])).
% 2.60/2.84  thf('234', plain,
% 2.60/2.84      (![X6 : $i, X7 : $i]:
% 2.60/2.84         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 2.60/2.84          | (v1_relat_1 @ X6)
% 2.60/2.84          | ~ (v1_relat_1 @ X7))),
% 2.60/2.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.60/2.84  thf('235', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 2.60/2.84        | (v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['233', '234'])).
% 2.60/2.84  thf('236', plain,
% 2.60/2.84      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 2.60/2.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.60/2.84  thf('237', plain,
% 2.60/2.84      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['235', '236'])).
% 2.60/2.84  thf('238', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('239', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(redefinition_k1_partfun1, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.60/2.84     ( ( ( v1_funct_1 @ E ) & 
% 2.60/2.84         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.60/2.84         ( v1_funct_1 @ F ) & 
% 2.60/2.84         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.60/2.84       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.60/2.84  thf('240', plain,
% 2.60/2.84      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 2.60/2.84         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 2.60/2.84          | ~ (v1_funct_1 @ X56)
% 2.60/2.84          | ~ (v1_funct_1 @ X59)
% 2.60/2.84          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 2.60/2.84          | ((k1_partfun1 @ X57 @ X58 @ X60 @ X61 @ X56 @ X59)
% 2.60/2.84              = (k5_relat_1 @ X56 @ X59)))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.60/2.84  thf('241', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.84         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.60/2.84            = (k5_relat_1 @ sk_C @ X0))
% 2.60/2.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.60/2.84          | ~ (v1_funct_1 @ X0)
% 2.60/2.84          | ~ (v1_funct_1 @ sk_C))),
% 2.60/2.84      inference('sup-', [status(thm)], ['239', '240'])).
% 2.60/2.84  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('243', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.84         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.60/2.84            = (k5_relat_1 @ sk_C @ X0))
% 2.60/2.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.60/2.84          | ~ (v1_funct_1 @ X0))),
% 2.60/2.84      inference('demod', [status(thm)], ['241', '242'])).
% 2.60/2.84  thf('244', plain,
% 2.60/2.84      ((~ (v1_funct_1 @ sk_D)
% 2.60/2.84        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.60/2.84            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['238', '243'])).
% 2.60/2.84  thf('245', plain, ((v1_funct_1 @ sk_D)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('246', plain,
% 2.60/2.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.60/2.84         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['244', '245'])).
% 2.60/2.84  thf('247', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['237', '246'])).
% 2.60/2.84  thf('248', plain,
% 2.60/2.84      (((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 2.60/2.84         = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C)))),
% 2.60/2.84      inference('demod', [status(thm)], ['224', '247'])).
% 2.60/2.84  thf('249', plain,
% 2.60/2.84      (![X17 : $i, X18 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X17)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ X17) @ (k4_relat_1 @ X18)))
% 2.60/2.84          | ~ (v1_relat_1 @ X18))),
% 2.60/2.84      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.60/2.84  thf(t64_funct_1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.60/2.84       ( ![B:$i]:
% 2.60/2.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.60/2.84           ( ( ( v2_funct_1 @ A ) & 
% 2.60/2.84               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 2.60/2.84               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 2.60/2.84             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.60/2.84  thf('250', plain,
% 2.60/2.84      (![X31 : $i, X32 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X31)
% 2.60/2.84          | ~ (v1_funct_1 @ X31)
% 2.60/2.84          | ((X31) = (k2_funct_1 @ X32))
% 2.60/2.84          | ((k5_relat_1 @ X31 @ X32) != (k6_relat_1 @ (k2_relat_1 @ X32)))
% 2.60/2.84          | ((k2_relat_1 @ X31) != (k1_relat_1 @ X32))
% 2.60/2.84          | ~ (v2_funct_1 @ X32)
% 2.60/2.84          | ~ (v1_funct_1 @ X32)
% 2.60/2.84          | ~ (v1_relat_1 @ X32))),
% 2.60/2.84      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.60/2.84  thf('251', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.60/2.84  thf('252', plain,
% 2.60/2.84      (![X31 : $i, X32 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X31)
% 2.60/2.84          | ~ (v1_funct_1 @ X31)
% 2.60/2.84          | ((X31) = (k2_funct_1 @ X32))
% 2.60/2.84          | ((k5_relat_1 @ X31 @ X32) != (k6_partfun1 @ (k2_relat_1 @ X32)))
% 2.60/2.84          | ((k2_relat_1 @ X31) != (k1_relat_1 @ X32))
% 2.60/2.84          | ~ (v2_funct_1 @ X32)
% 2.60/2.84          | ~ (v1_funct_1 @ X32)
% 2.60/2.84          | ~ (v1_relat_1 @ X32))),
% 2.60/2.84      inference('demod', [status(thm)], ['250', '251'])).
% 2.60/2.84  thf('253', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 2.60/2.84            != (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ X1))))
% 2.60/2.84          | ~ (v1_relat_1 @ X1)
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 2.60/2.84          | ~ (v1_funct_1 @ (k4_relat_1 @ X1))
% 2.60/2.84          | ~ (v2_funct_1 @ (k4_relat_1 @ X1))
% 2.60/2.84          | ((k2_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.84              != (k1_relat_1 @ (k4_relat_1 @ X1)))
% 2.60/2.84          | ((k4_relat_1 @ X0) = (k2_funct_1 @ (k4_relat_1 @ X1)))
% 2.60/2.84          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['249', '252'])).
% 2.60/2.84  thf('254', plain,
% 2.60/2.84      ((((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 2.60/2.84          != (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 2.60/2.84        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 2.60/2.84        | ((k4_relat_1 @ (k4_relat_1 @ sk_C))
% 2.60/2.84            = (k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 2.60/2.84        | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 2.60/2.84            != (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 2.60/2.84        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 2.60/2.84        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['248', '253'])).
% 2.60/2.84  thf('255', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['210', '211'])).
% 2.60/2.84  thf('256', plain,
% 2.60/2.84      (![X11 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k4_relat_1 @ X11)) = (X11)) | ~ (v1_relat_1 @ X11))),
% 2.60/2.84      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.60/2.84  thf('257', plain,
% 2.60/2.84      (![X17 : $i, X18 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X17)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ X17) @ (k4_relat_1 @ X18)))
% 2.60/2.84          | ~ (v1_relat_1 @ X18))),
% 2.60/2.84      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.60/2.84  thf('258', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 2.60/2.84            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.84          | ~ (v1_relat_1 @ X1))),
% 2.60/2.84      inference('sup+', [status(thm)], ['256', '257'])).
% 2.60/2.84  thf('259', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ sk_C)
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.60/2.84          | ((k4_relat_1 @ 
% 2.60/2.84              (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ X0))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ sk_C))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['255', '258'])).
% 2.60/2.84  thf('260', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('261', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['195', '196', '197'])).
% 2.60/2.84  thf('262', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['210', '211'])).
% 2.60/2.84  thf('263', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ sk_C @ X0))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ sk_C))))),
% 2.60/2.84      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 2.60/2.84  thf('264', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['143', '144', '145'])).
% 2.60/2.84  thf('265', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 2.60/2.84            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.60/2.84          | ~ (v1_relat_1 @ X1))),
% 2.60/2.84      inference('sup+', [status(thm)], ['256', '257'])).
% 2.60/2.84  thf('266', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (v1_relat_1 @ sk_D)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ X0))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ X0) @ sk_D)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['264', '265'])).
% 2.60/2.84  thf('267', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('268', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X0)
% 2.60/2.84          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ X0))
% 2.60/2.84              = (k5_relat_1 @ (k4_relat_1 @ X0) @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['266', '267'])).
% 2.60/2.84  thf('269', plain,
% 2.60/2.84      ((((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 2.60/2.84          = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_D))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D)
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.60/2.84      inference('sup+', [status(thm)], ['263', '268'])).
% 2.60/2.84  thf('270', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['210', '211'])).
% 2.60/2.84  thf('271', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('272', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['195', '196', '197'])).
% 2.60/2.84  thf('273', plain,
% 2.60/2.84      (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 2.60/2.84         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['269', '270', '271', '272'])).
% 2.60/2.84  thf('274', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('275', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['54', '57', '58', '59', '60'])).
% 2.60/2.84  thf('276', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['210', '211'])).
% 2.60/2.84  thf('277', plain, ((v1_relat_1 @ sk_C)),
% 2.60/2.84      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.84  thf('278', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['210', '211'])).
% 2.60/2.84  thf('279', plain, ((v1_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('280', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['210', '211'])).
% 2.60/2.84  thf('281', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('282', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['210', '211'])).
% 2.60/2.84  thf('283', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('284', plain,
% 2.60/2.84      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.60/2.84         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 2.60/2.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.60/2.84  thf('285', plain,
% 2.60/2.84      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.60/2.84      inference('sup-', [status(thm)], ['283', '284'])).
% 2.60/2.84  thf('286', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('287', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.60/2.84      inference('sup+', [status(thm)], ['285', '286'])).
% 2.60/2.84  thf('288', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('289', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('290', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('291', plain, ((v1_funct_1 @ sk_D)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('292', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['153', '154', '155', '160', '161', '162', '163'])).
% 2.60/2.84  thf('293', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('294', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['195', '196', '197'])).
% 2.60/2.84  thf('295', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['143', '144', '145'])).
% 2.60/2.84  thf('296', plain,
% 2.60/2.84      ((((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))
% 2.60/2.84        | ((sk_C) = (k2_funct_1 @ sk_D))
% 2.60/2.84        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['254', '273', '274', '275', '276', '277', '278', '279', 
% 2.60/2.84                 '280', '281', '282', '287', '288', '289', '290', '291', 
% 2.60/2.84                 '292', '293', '294', '295'])).
% 2.60/2.84  thf('297', plain,
% 2.60/2.84      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.60/2.84        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.60/2.84        (k6_partfun1 @ sk_A))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('298', plain,
% 2.60/2.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.60/2.84         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['244', '245'])).
% 2.60/2.84  thf('299', plain,
% 2.60/2.84      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.60/2.84        (k6_partfun1 @ sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['297', '298'])).
% 2.60/2.84  thf('300', plain,
% 2.60/2.84      ((m1_subset_1 @ 
% 2.60/2.84        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.60/2.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.60/2.84      inference('demod', [status(thm)], ['231', '232'])).
% 2.60/2.84  thf('301', plain,
% 2.60/2.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.60/2.84         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['244', '245'])).
% 2.60/2.84  thf('302', plain,
% 2.60/2.84      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.60/2.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.60/2.84      inference('demod', [status(thm)], ['300', '301'])).
% 2.60/2.84  thf(redefinition_r2_relset_1, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i,D:$i]:
% 2.60/2.84     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.60/2.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.60/2.84       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.60/2.84  thf('303', plain,
% 2.60/2.84      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.60/2.84         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 2.60/2.84          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 2.60/2.84          | ((X44) = (X47))
% 2.60/2.84          | ~ (r2_relset_1 @ X45 @ X46 @ X44 @ X47))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.60/2.84  thf('304', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.60/2.84          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.60/2.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['302', '303'])).
% 2.60/2.84  thf('305', plain,
% 2.60/2.84      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.60/2.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.60/2.84        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['299', '304'])).
% 2.60/2.84  thf(dt_k6_partfun1, axiom,
% 2.60/2.84    (![A:$i]:
% 2.60/2.84     ( ( m1_subset_1 @
% 2.60/2.84         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.60/2.84       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.60/2.84  thf('306', plain,
% 2.60/2.84      (![X55 : $i]:
% 2.60/2.84         (m1_subset_1 @ (k6_partfun1 @ X55) @ 
% 2.60/2.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X55)))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.60/2.84  thf('307', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['305', '306'])).
% 2.60/2.84  thf('308', plain,
% 2.60/2.84      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 2.60/2.84        | ((sk_C) = (k2_funct_1 @ sk_D))
% 2.60/2.84        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['296', '307'])).
% 2.60/2.84  thf('309', plain,
% 2.60/2.84      ((~ (v2_funct_1 @ sk_D)
% 2.60/2.84        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.60/2.84        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.60/2.84      inference('simplify', [status(thm)], ['308'])).
% 2.60/2.84  thf('310', plain,
% 2.60/2.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.60/2.84         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['244', '245'])).
% 2.60/2.84  thf('311', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['305', '306'])).
% 2.60/2.84  thf('312', plain,
% 2.60/2.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.60/2.84         = (k6_partfun1 @ sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['310', '311'])).
% 2.60/2.84  thf('313', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(t30_funct_2, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i,D:$i]:
% 2.60/2.84     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.60/2.84         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.60/2.84       ( ![E:$i]:
% 2.60/2.84         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.60/2.84             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.60/2.84           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.60/2.84               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.60/2.84             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.60/2.84               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.60/2.84  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.60/2.84  thf(zf_stmt_2, axiom,
% 2.60/2.84    (![C:$i,B:$i]:
% 2.60/2.84     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.60/2.84       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.60/2.84  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.60/2.84  thf(zf_stmt_4, axiom,
% 2.60/2.84    (![E:$i,D:$i]:
% 2.60/2.84     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.60/2.84  thf(zf_stmt_5, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i,D:$i]:
% 2.60/2.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.60/2.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.60/2.84       ( ![E:$i]:
% 2.60/2.84         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.60/2.84             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.60/2.84           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.60/2.84               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.60/2.84             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.60/2.84  thf('314', plain,
% 2.60/2.84      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i, X75 : $i]:
% 2.60/2.84         (~ (v1_funct_1 @ X71)
% 2.60/2.84          | ~ (v1_funct_2 @ X71 @ X72 @ X73)
% 2.60/2.84          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73)))
% 2.60/2.84          | (zip_tseitin_0 @ X71 @ X74)
% 2.60/2.84          | ~ (v2_funct_1 @ (k1_partfun1 @ X75 @ X72 @ X72 @ X73 @ X74 @ X71))
% 2.60/2.84          | (zip_tseitin_1 @ X73 @ X72)
% 2.60/2.84          | ((k2_relset_1 @ X75 @ X72 @ X74) != (X72))
% 2.60/2.84          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X72)))
% 2.60/2.84          | ~ (v1_funct_2 @ X74 @ X75 @ X72)
% 2.60/2.84          | ~ (v1_funct_1 @ X74))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.60/2.84  thf('315', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (~ (v1_funct_1 @ X0)
% 2.60/2.84          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.60/2.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.60/2.84          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.60/2.84          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.60/2.84          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.60/2.84          | (zip_tseitin_0 @ sk_D @ X0)
% 2.60/2.84          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.60/2.84          | ~ (v1_funct_1 @ sk_D))),
% 2.60/2.84      inference('sup-', [status(thm)], ['313', '314'])).
% 2.60/2.84  thf('316', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('317', plain, ((v1_funct_1 @ sk_D)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('318', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (~ (v1_funct_1 @ X0)
% 2.60/2.84          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.60/2.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.60/2.84          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.60/2.84          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.60/2.84          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.60/2.84          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.60/2.84      inference('demod', [status(thm)], ['315', '316', '317'])).
% 2.60/2.84  thf('319', plain,
% 2.60/2.84      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.60/2.84        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.60/2.84        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.60/2.84        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.60/2.84        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.60/2.84        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.60/2.84        | ~ (v1_funct_1 @ sk_C))),
% 2.60/2.84      inference('sup-', [status(thm)], ['312', '318'])).
% 2.60/2.84  thf('320', plain, (![X27 : $i]: (v2_funct_1 @ (k6_relat_1 @ X27))),
% 2.60/2.84      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.60/2.84  thf('321', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.60/2.84  thf('322', plain, (![X27 : $i]: (v2_funct_1 @ (k6_partfun1 @ X27))),
% 2.60/2.84      inference('demod', [status(thm)], ['320', '321'])).
% 2.60/2.84  thf('323', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('324', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('325', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('326', plain, ((v1_funct_1 @ sk_C)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('327', plain,
% 2.60/2.84      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.60/2.84        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.60/2.84        | ((sk_B) != (sk_B)))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['319', '322', '323', '324', '325', '326'])).
% 2.60/2.84  thf('328', plain,
% 2.60/2.84      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.60/2.84      inference('simplify', [status(thm)], ['327'])).
% 2.60/2.84  thf('329', plain,
% 2.60/2.84      (![X69 : $i, X70 : $i]:
% 2.60/2.84         (((X69) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X69 @ X70))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.60/2.84  thf('330', plain,
% 2.60/2.84      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['328', '329'])).
% 2.60/2.84  thf('331', plain, (((sk_A) != (k1_xboole_0))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('332', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.60/2.84      inference('simplify_reflect-', [status(thm)], ['330', '331'])).
% 2.60/2.84  thf('333', plain,
% 2.60/2.84      (![X67 : $i, X68 : $i]:
% 2.60/2.84         ((v2_funct_1 @ X68) | ~ (zip_tseitin_0 @ X68 @ X67))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.60/2.84  thf('334', plain, ((v2_funct_1 @ sk_D)),
% 2.60/2.84      inference('sup-', [status(thm)], ['332', '333'])).
% 2.60/2.84  thf('335', plain,
% 2.60/2.84      ((((sk_B) != (k1_relat_1 @ sk_D)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['309', '334'])).
% 2.60/2.84  thf('336', plain, ((v1_funct_1 @ sk_D)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('337', plain,
% 2.60/2.84      (![X24 : $i]:
% 2.60/2.84         (~ (v2_funct_1 @ X24)
% 2.60/2.84          | ((k2_funct_1 @ X24) = (k4_relat_1 @ X24))
% 2.60/2.84          | ~ (v1_funct_1 @ X24)
% 2.60/2.84          | ~ (v1_relat_1 @ X24))),
% 2.60/2.84      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.60/2.84  thf('338', plain,
% 2.60/2.84      ((~ (v1_relat_1 @ sk_D)
% 2.60/2.84        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_D))),
% 2.60/2.84      inference('sup-', [status(thm)], ['336', '337'])).
% 2.60/2.84  thf('339', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('340', plain,
% 2.60/2.84      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['338', '339'])).
% 2.60/2.84  thf('341', plain, ((v2_funct_1 @ sk_D)),
% 2.60/2.84      inference('sup-', [status(thm)], ['332', '333'])).
% 2.60/2.84  thf('342', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['340', '341'])).
% 2.60/2.84  thf('343', plain,
% 2.60/2.84      ((((sk_B) != (k1_relat_1 @ sk_D)) | ((sk_C) = (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['335', '342'])).
% 2.60/2.84  thf('344', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(t35_funct_2, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i]:
% 2.60/2.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.60/2.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.60/2.84       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.60/2.84         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.60/2.84           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.60/2.84             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.60/2.84  thf('345', plain,
% 2.60/2.84      (![X79 : $i, X80 : $i, X81 : $i]:
% 2.60/2.84         (((X79) = (k1_xboole_0))
% 2.60/2.84          | ~ (v1_funct_1 @ X80)
% 2.60/2.84          | ~ (v1_funct_2 @ X80 @ X81 @ X79)
% 2.60/2.84          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X79)))
% 2.60/2.84          | ((k5_relat_1 @ X80 @ (k2_funct_1 @ X80)) = (k6_partfun1 @ X81))
% 2.60/2.84          | ~ (v2_funct_1 @ X80)
% 2.60/2.84          | ((k2_relset_1 @ X81 @ X79 @ X80) != (X79)))),
% 2.60/2.84      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.60/2.84  thf('346', plain,
% 2.60/2.84      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_D)
% 2.60/2.84        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.60/2.84        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.60/2.84        | ~ (v1_funct_1 @ sk_D)
% 2.60/2.84        | ((sk_A) = (k1_xboole_0)))),
% 2.60/2.84      inference('sup-', [status(thm)], ['344', '345'])).
% 2.60/2.84  thf('347', plain,
% 2.60/2.84      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup-', [status(thm)], ['55', '56'])).
% 2.60/2.84  thf('348', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('349', plain, ((v1_funct_1 @ sk_D)),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('350', plain,
% 2.60/2.84      ((((k2_relat_1 @ sk_D) != (sk_A))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_D)
% 2.60/2.84        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.60/2.84        | ((sk_A) = (k1_xboole_0)))),
% 2.60/2.84      inference('demod', [status(thm)], ['346', '347', '348', '349'])).
% 2.60/2.84  thf('351', plain, (((sk_A) != (k1_xboole_0))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('352', plain,
% 2.60/2.84      ((((k2_relat_1 @ sk_D) != (sk_A))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_D)
% 2.60/2.84        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 2.60/2.84      inference('simplify_reflect-', [status(thm)], ['350', '351'])).
% 2.60/2.84  thf('353', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.60/2.84      inference('demod', [status(thm)], ['54', '57', '58', '59', '60'])).
% 2.60/2.84  thf('354', plain,
% 2.60/2.84      ((((sk_A) != (sk_A))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_D)
% 2.60/2.84        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 2.60/2.84      inference('demod', [status(thm)], ['352', '353'])).
% 2.60/2.84  thf('355', plain,
% 2.60/2.84      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.60/2.84        | ~ (v2_funct_1 @ sk_D))),
% 2.60/2.84      inference('simplify', [status(thm)], ['354'])).
% 2.60/2.84  thf('356', plain, ((v2_funct_1 @ sk_D)),
% 2.60/2.84      inference('sup-', [status(thm)], ['332', '333'])).
% 2.60/2.84  thf('357', plain,
% 2.60/2.84      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 2.60/2.84      inference('demod', [status(thm)], ['355', '356'])).
% 2.60/2.84  thf('358', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['340', '341'])).
% 2.60/2.84  thf('359', plain,
% 2.60/2.84      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 2.60/2.84      inference('demod', [status(thm)], ['357', '358'])).
% 2.60/2.84  thf('360', plain,
% 2.60/2.84      (![X15 : $i, X16 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X15)
% 2.60/2.84          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X16 @ X15)) @ 
% 2.60/2.84             (k2_relat_1 @ X15))
% 2.60/2.84          | ~ (v1_relat_1 @ X16))),
% 2.60/2.84      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.60/2.84  thf('361', plain,
% 2.60/2.84      (![X0 : $i, X2 : $i]:
% 2.60/2.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.60/2.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.60/2.84  thf('362', plain,
% 2.60/2.84      (![X0 : $i, X1 : $i]:
% 2.60/2.84         (~ (v1_relat_1 @ X1)
% 2.60/2.84          | ~ (v1_relat_1 @ X0)
% 2.60/2.84          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.60/2.84               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.60/2.84          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.60/2.84      inference('sup-', [status(thm)], ['360', '361'])).
% 2.60/2.84  thf('363', plain,
% 2.60/2.84      ((~ (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ sk_D)) @ 
% 2.60/2.84           (k2_relat_1 @ (k6_partfun1 @ sk_B)))
% 2.60/2.84        | ((k2_relat_1 @ (k4_relat_1 @ sk_D))
% 2.60/2.84            = (k2_relat_1 @ (k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D))))
% 2.60/2.84        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 2.60/2.84        | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup-', [status(thm)], ['359', '362'])).
% 2.60/2.84  thf('364', plain,
% 2.60/2.84      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['128', '129'])).
% 2.60/2.84  thf('365', plain,
% 2.60/2.84      (![X20 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 2.60/2.84      inference('demod', [status(thm)], ['69', '70'])).
% 2.60/2.84  thf('366', plain,
% 2.60/2.84      (![X13 : $i]:
% 2.60/2.84         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 2.60/2.84          | ~ (v1_relat_1 @ X13))),
% 2.60/2.84      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.60/2.84  thf('367', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(dt_k8_relset_1, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i,D:$i]:
% 2.60/2.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.60/2.84       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.60/2.84  thf('368', plain,
% 2.60/2.84      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.60/2.84         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.60/2.84          | (m1_subset_1 @ (k8_relset_1 @ X34 @ X35 @ X33 @ X36) @ 
% 2.60/2.84             (k1_zfmisc_1 @ X34)))),
% 2.60/2.84      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 2.60/2.84  thf('369', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         (m1_subset_1 @ (k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 2.60/2.84          (k1_zfmisc_1 @ sk_B))),
% 2.60/2.84      inference('sup-', [status(thm)], ['367', '368'])).
% 2.60/2.84  thf('370', plain,
% 2.60/2.84      (![X3 : $i, X4 : $i]:
% 2.60/2.84         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 2.60/2.84      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.84  thf('371', plain,
% 2.60/2.84      (![X0 : $i]: (r1_tarski @ (k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0) @ sk_B)),
% 2.60/2.84      inference('sup-', [status(thm)], ['369', '370'])).
% 2.60/2.84  thf('372', plain,
% 2.60/2.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf(redefinition_k8_relset_1, axiom,
% 2.60/2.84    (![A:$i,B:$i,C:$i,D:$i]:
% 2.60/2.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.60/2.84       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.60/2.84  thf('373', plain,
% 2.60/2.84      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.60/2.84         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.60/2.84          | ((k8_relset_1 @ X41 @ X42 @ X40 @ X43) = (k10_relat_1 @ X40 @ X43)))),
% 2.60/2.84      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.60/2.84  thf('374', plain,
% 2.60/2.84      (![X0 : $i]:
% 2.60/2.84         ((k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 2.60/2.84      inference('sup-', [status(thm)], ['372', '373'])).
% 2.60/2.84  thf('375', plain,
% 2.60/2.84      (![X0 : $i]: (r1_tarski @ (k10_relat_1 @ sk_D @ X0) @ sk_B)),
% 2.60/2.84      inference('demod', [status(thm)], ['371', '374'])).
% 2.60/2.84  thf('376', plain,
% 2.60/2.84      (((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B) | ~ (v1_relat_1 @ sk_D))),
% 2.60/2.84      inference('sup+', [status(thm)], ['366', '375'])).
% 2.60/2.84  thf('377', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('378', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 2.60/2.84      inference('demod', [status(thm)], ['376', '377'])).
% 2.60/2.84  thf('379', plain,
% 2.60/2.84      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['128', '129'])).
% 2.60/2.84  thf('380', plain,
% 2.60/2.84      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 2.60/2.84      inference('demod', [status(thm)], ['357', '358'])).
% 2.60/2.84  thf('381', plain,
% 2.60/2.84      (![X20 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 2.60/2.84      inference('demod', [status(thm)], ['69', '70'])).
% 2.60/2.84  thf('382', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['143', '144', '145'])).
% 2.60/2.84  thf('383', plain, ((v1_relat_1 @ sk_D)),
% 2.60/2.84      inference('demod', [status(thm)], ['93', '94'])).
% 2.60/2.84  thf('384', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 2.60/2.84      inference('demod', [status(thm)],
% 2.60/2.84                ['363', '364', '365', '378', '379', '380', '381', '382', '383'])).
% 2.60/2.84  thf('385', plain, ((((sk_B) != (sk_B)) | ((sk_C) = (k4_relat_1 @ sk_D)))),
% 2.60/2.84      inference('demod', [status(thm)], ['343', '384'])).
% 2.60/2.84  thf('386', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 2.60/2.84      inference('simplify', [status(thm)], ['385'])).
% 2.60/2.84  thf('387', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 2.60/2.84      inference('demod', [status(thm)], ['164', '386'])).
% 2.60/2.84  thf('388', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.60/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.84  thf('389', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['177', '182', '183'])).
% 2.60/2.84  thf('390', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 2.60/2.84      inference('demod', [status(thm)], ['388', '389'])).
% 2.60/2.84  thf('391', plain, ($false),
% 2.60/2.84      inference('simplify_reflect-', [status(thm)], ['387', '390'])).
% 2.60/2.84  
% 2.60/2.84  % SZS output end Refutation
% 2.60/2.84  
% 2.60/2.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
