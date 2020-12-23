%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WZtnjOPvDx

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:33 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 147 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  538 (1928 expanded)
%              Number of equality atoms :   25 (  69 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t200_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v5_relat_1 @ C @ A )
                & ( v1_funct_1 @ C ) )
             => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) )
                = ( k1_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_funct_2 @ B @ A @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v5_relat_1 @ C @ A )
                  & ( v1_funct_1 @ C ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) )
                  = ( k1_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t200_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X26 ) @ X27 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ( ( k8_relset_1 @ X23 @ X25 @ X24 @ X25 )
        = X23 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('12',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( v1_funct_2 @ X26 @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','15','21','22'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k10_relat_1 @ X3 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('25',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['37','38'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','45'])).

thf('47',plain,(
    ( k10_relat_1 @ sk_C @ sk_A )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','46'])).

thf('48',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','47'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WZtnjOPvDx
% 0.15/0.38  % Computer   : n015.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:19:23 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 81 iterations in 0.139s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.63  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.45/0.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.63  thf(t200_funct_2, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.45/0.63             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.45/0.63                 ( v1_funct_1 @ C ) ) =>
% 0.45/0.63               ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) = ( k1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.63          ( ![B:$i]:
% 0.45/0.63            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.45/0.63                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.45/0.63              ( ![C:$i]:
% 0.45/0.63                ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.45/0.63                    ( v1_funct_1 @ C ) ) =>
% 0.45/0.63                  ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) =
% 0.45/0.63                    ( k1_relat_1 @ C ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t200_funct_2])).
% 0.45/0.63  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d19_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v5_relat_1 @ X0 @ X1)
% 0.45/0.63          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.45/0.63          | ~ (v1_relat_1 @ X0))),
% 0.45/0.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf(t4_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.63       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.45/0.63         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.45/0.63           ( m1_subset_1 @
% 0.45/0.63             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X26 : $i, X27 : $i]:
% 0.45/0.63         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.45/0.63          | (m1_subset_1 @ X26 @ 
% 0.45/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X26) @ X27)))
% 0.45/0.63          | ~ (v1_funct_1 @ X26)
% 0.45/0.63          | ~ (v1_relat_1 @ X26))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_C @ 
% 0.45/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.45/0.63  thf(t48_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.63         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.63         (((X25) = (k1_xboole_0))
% 0.45/0.63          | ~ (v1_funct_1 @ X24)
% 0.45/0.63          | ~ (v1_funct_2 @ X24 @ X23 @ X25)
% 0.45/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 0.45/0.63          | ((k8_relset_1 @ X23 @ X25 @ X24 @ X25) = (X23)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ sk_A)
% 0.45/0.63          = (k1_relat_1 @ sk_C))
% 0.45/0.63        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_A)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.45/0.63  thf(redefinition_k8_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.45/0.63          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.45/0.63           = (k10_relat_1 @ sk_C @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X26 : $i, X27 : $i]:
% 0.45/0.63         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.45/0.63          | (v1_funct_2 @ X26 @ (k1_relat_1 @ X26) @ X27)
% 0.45/0.63          | ~ (v1_funct_1 @ X26)
% 0.45/0.63          | ~ (v1_relat_1 @ X26))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.63        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('21', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.45/0.63  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      ((((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))
% 0.45/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['12', '15', '21', '22'])).
% 0.45/0.63  thf(t182_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( v1_relat_1 @ B ) =>
% 0.45/0.63           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.45/0.63             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X2)
% 0.45/0.63          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.45/0.63              = (k10_relat_1 @ X3 @ (k1_relat_1 @ X2)))
% 0.45/0.63          | ~ (v1_relat_1 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      ((((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))
% 0.45/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.63  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc1_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( v1_relat_1 @ C ) ))).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.63         ((v1_relat_1 @ X5)
% 0.45/0.63          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.63  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['26', '27', '30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc5_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.63       ( ![C:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.63             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.45/0.63          | (v1_partfun1 @ X15 @ X16)
% 0.45/0.63          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.45/0.63          | ~ (v1_funct_1 @ X15)
% 0.45/0.63          | (v1_xboole_0 @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (((v1_xboole_0 @ sk_A)
% 0.45/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.45/0.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.45/0.63        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('36', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('37', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.45/0.63  thf('38', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('39', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.45/0.63      inference('clc', [status(thm)], ['37', '38'])).
% 0.45/0.63  thf(d4_partfun1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.63       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (v1_partfun1 @ X22 @ X21)
% 0.45/0.63          | ((k1_relat_1 @ X22) = (X21))
% 0.45/0.63          | ~ (v4_relat_1 @ X22 @ X21)
% 0.45/0.63          | ~ (v1_relat_1 @ X22))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.45/0.63        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.45/0.63        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.63  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.63         ((v4_relat_1 @ X8 @ X9)
% 0.45/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.63  thf('45', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.63  thf('46', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['41', '42', '45'])).
% 0.45/0.63  thf('47', plain, (((k10_relat_1 @ sk_C @ sk_A) != (k1_relat_1 @ sk_C))),
% 0.45/0.63      inference('demod', [status(thm)], ['31', '46'])).
% 0.45/0.63  thf('48', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['23', '47'])).
% 0.45/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.63  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.63  thf('50', plain, ($false),
% 0.45/0.63      inference('demod', [status(thm)], ['0', '48', '49'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
