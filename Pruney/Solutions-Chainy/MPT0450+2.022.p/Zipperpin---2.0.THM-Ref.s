%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.56IGNXH9S0

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:04 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 123 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  548 (1031 expanded)
%              Number of equality atoms :   18 (  56 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X10 ) ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) )
      = ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k3_relat_1 @ X25 ) @ ( k3_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','22'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k3_relat_1 @ X25 ) @ ( k3_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('30',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','33'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','38'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.56IGNXH9S0
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 207 iterations in 0.100s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.38/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(t51_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.38/0.55       ( A ) ))).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 0.38/0.55           = (X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.38/0.55  thf(t12_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12)) @ 
% 0.38/0.55           (k4_xboole_0 @ X11 @ X12)) = (X11))),
% 0.38/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf(t31_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( r1_tarski @
% 0.38/0.55       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.38/0.55       ( k2_xboole_0 @ B @ C ) ))).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.55         (r1_tarski @ 
% 0.38/0.55          (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)) @ 
% 0.38/0.55          (k2_xboole_0 @ X9 @ X10))),
% 0.38/0.55      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.55         (r1_tarski @ 
% 0.38/0.55          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ 
% 0.38/0.55           (k1_setfam_1 @ (k2_tarski @ X8 @ X10))) @ 
% 0.38/0.55          (k2_xboole_0 @ X9 @ X10))),
% 0.38/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.55  thf(t23_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.38/0.55       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.55         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 0.38/0.55           = (k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X7)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))
% 0.38/0.55           = (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6)) @ 
% 0.38/0.55              (k1_setfam_1 @ (k2_tarski @ X5 @ X7))))),
% 0.38/0.55      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.55         (r1_tarski @ 
% 0.38/0.55          (k1_setfam_1 @ (k2_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))) @ 
% 0.38/0.55          (k2_xboole_0 @ X9 @ X10))),
% 0.38/0.55      inference('demod', [status(thm)], ['6', '11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0)) @ 
% 0.38/0.55          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.38/0.55           (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['2', '12'])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12)) @ 
% 0.38/0.55           (k4_xboole_0 @ X11 @ X12)) = (X11))),
% 0.38/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X0 : $i, X2 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0)) @ X0)),
% 0.38/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.55  thf(t31_relat_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( v1_relat_1 @ B ) =>
% 0.38/0.55           ( ( r1_tarski @ A @ B ) =>
% 0.38/0.55             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X24 : $i, X25 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X24)
% 0.38/0.55          | (r1_tarski @ (k3_relat_1 @ X25) @ (k3_relat_1 @ X24))
% 0.38/0.55          | ~ (r1_tarski @ X25 @ X24)
% 0.38/0.55          | ~ (v1_relat_1 @ X25))),
% 0.38/0.55      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.38/0.55             (k3_relat_1 @ X0))
% 0.38/0.55          | ~ (v1_relat_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X0 : $i, X2 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0)) @ X0)),
% 0.38/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.55  thf(t3_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X19 : $i, X21 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.38/0.55          (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.55  thf(cc2_relat_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (![X22 : $i, X23 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.38/0.55          | (v1_relat_1 @ X22)
% 0.38/0.55          | ~ (v1_relat_1 @ X23))),
% 0.38/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.38/0.55             (k3_relat_1 @ X0)))),
% 0.38/0.55      inference('clc', [status(thm)], ['17', '22'])).
% 0.38/0.55  thf(t17_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.38/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.38/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X24 : $i, X25 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X24)
% 0.38/0.55          | (r1_tarski @ (k3_relat_1 @ X25) @ (k3_relat_1 @ X24))
% 0.38/0.55          | ~ (r1_tarski @ X25 @ X24)
% 0.38/0.55          | ~ (v1_relat_1 @ X25))),
% 0.38/0.55      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.38/0.55             (k3_relat_1 @ X0))
% 0.38/0.55          | ~ (v1_relat_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.38/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X19 : $i, X21 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.38/0.55          (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (![X22 : $i, X23 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.38/0.55          | (v1_relat_1 @ X22)
% 0.38/0.55          | ~ (v1_relat_1 @ X23))),
% 0.38/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.38/0.55             (k3_relat_1 @ X0)))),
% 0.38/0.55      inference('clc', [status(thm)], ['28', '33'])).
% 0.38/0.55  thf(t19_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.38/0.55       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X2 @ X3)
% 0.38/0.55          | ~ (r1_tarski @ X2 @ X4)
% 0.38/0.55          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X2 @ X3)
% 0.38/0.55          | ~ (r1_tarski @ X2 @ X4)
% 0.38/0.55          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.38/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.38/0.55             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X0) @ X2)))
% 0.38/0.55          | ~ (r1_tarski @ 
% 0.38/0.55               (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.38/0.55      inference('sup-', [status(thm)], ['34', '37'])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.38/0.55             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0))))
% 0.38/0.55          | ~ (v1_relat_1 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['23', '38'])).
% 0.38/0.55  thf(t34_relat_1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( v1_relat_1 @ B ) =>
% 0.38/0.55           ( r1_tarski @
% 0.38/0.55             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.38/0.55             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( v1_relat_1 @ A ) =>
% 0.38/0.55          ( ![B:$i]:
% 0.38/0.55            ( ( v1_relat_1 @ B ) =>
% 0.38/0.55              ( r1_tarski @
% 0.38/0.55                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.38/0.55                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.38/0.55          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (~ (r1_tarski @ 
% 0.38/0.55          (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.38/0.55          (k1_setfam_1 @ 
% 0.38/0.55           (k2_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))))),
% 0.38/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.38/0.55  thf('44', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['39', '43'])).
% 0.38/0.55  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('47', plain, ($false),
% 0.38/0.55      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
