%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C25K2ktSoh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 150 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  540 (1866 expanded)
%              Number of equality atoms :   24 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

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

thf('1',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['16','17'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X26 ) @ X27 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('37',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','40','43'])).

thf('45',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','25','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C25K2ktSoh
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:58:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 62 iterations in 0.044s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(t182_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( v1_relat_1 @ B ) =>
% 0.22/0.52           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.22/0.52             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X6)
% 0.22/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.22/0.52              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.22/0.52          | ~ (v1_relat_1 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.22/0.52  thf(t200_funct_2, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.22/0.52                 ( v1_funct_1 @ C ) ) =>
% 0.22/0.52               ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) = ( k1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.22/0.52                    ( v1_funct_1 @ C ) ) =>
% 0.22/0.52                  ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) =
% 0.22/0.52                    ( k1_relat_1 @ C ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t200_funct_2])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      ((((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.22/0.52          | (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf(fc6_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.52  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc5_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.52             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.22/0.52          | (v1_partfun1 @ X21 @ X22)
% 0.22/0.52          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.22/0.52          | ~ (v1_funct_1 @ X21)
% 0.22/0.52          | (v1_xboole_0 @ X23))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.52        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.52  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('18', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf(d4_partfun1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.52       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i]:
% 0.22/0.52         (~ (v1_partfun1 @ X25 @ X24)
% 0.22/0.52          | ((k1_relat_1 @ X25) = (X24))
% 0.22/0.52          | ~ (v4_relat_1 @ X25 @ X24)
% 0.22/0.52          | ~ (v1_relat_1 @ X25))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.52        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.22/0.52        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         ((v4_relat_1 @ X8 @ X9)
% 0.22/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('24', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.22/0.52  thf('26', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d19_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (v5_relat_1 @ X2 @ X3)
% 0.22/0.52          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.22/0.52          | ~ (v1_relat_1 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf(t4_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.52         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.22/0.52           ( m1_subset_1 @
% 0.22/0.52             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 0.22/0.52          | (m1_subset_1 @ X26 @ 
% 0.22/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X26) @ X27)))
% 0.22/0.52          | ~ (v1_funct_1 @ X26)
% 0.22/0.52          | ~ (v1_relat_1 @ X26))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.52        | (m1_subset_1 @ sk_C @ 
% 0.22/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.52  thf(t38_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.52         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.52         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.22/0.52            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.22/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.22/0.52      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ sk_A)
% 0.22/0.52         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.22/0.52          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.22/0.52           = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.22/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.52  thf('44', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['37', '40', '43'])).
% 0.22/0.52  thf('45', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['10', '25', '44'])).
% 0.22/0.52  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
