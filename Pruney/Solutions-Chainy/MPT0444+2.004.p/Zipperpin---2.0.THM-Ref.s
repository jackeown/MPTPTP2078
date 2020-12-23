%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FsdxieM4gF

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:45 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 151 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  529 (1111 expanded)
%              Number of equality atoms :   21 (  84 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X10 @ X12 ) ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) )
      = X7 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['7','14','15'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['7','14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','23'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) @ X2 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) @ X2 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','40'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FsdxieM4gF
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 527 iterations in 0.306s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.75  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.75  thf(t2_boole, axiom,
% 0.53/0.75    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.75  thf('0', plain,
% 0.53/0.75      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.75  thf(t12_setfam_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.75  thf('1', plain,
% 0.53/0.75      (![X15 : $i, X16 : $i]:
% 0.53/0.75         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      (![X9 : $i]:
% 0.53/0.75         ((k1_setfam_1 @ (k2_tarski @ X9 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.53/0.75      inference('demod', [status(thm)], ['0', '1'])).
% 0.53/0.75  thf(t31_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( r1_tarski @
% 0.53/0.75       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.53/0.75       ( k2_xboole_0 @ B @ C ) ))).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.75         (r1_tarski @ 
% 0.53/0.75          (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k3_xboole_0 @ X10 @ X12)) @ 
% 0.53/0.75          (k2_xboole_0 @ X11 @ X12))),
% 0.53/0.75      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.53/0.75  thf('4', plain,
% 0.53/0.75      (![X15 : $i, X16 : $i]:
% 0.53/0.75         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.75  thf('5', plain,
% 0.53/0.75      (![X15 : $i, X16 : $i]:
% 0.53/0.75         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.75  thf('6', plain,
% 0.53/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.75         (r1_tarski @ 
% 0.53/0.75          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X10 @ X11)) @ 
% 0.53/0.75           (k1_setfam_1 @ (k2_tarski @ X10 @ X12))) @ 
% 0.53/0.75          (k2_xboole_0 @ X11 @ X12))),
% 0.53/0.75      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.53/0.75  thf('7', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (r1_tarski @ 
% 0.53/0.75          (k2_xboole_0 @ k1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.53/0.75          (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['2', '6'])).
% 0.53/0.75  thf('8', plain,
% 0.53/0.75      (![X9 : $i]:
% 0.53/0.75         ((k1_setfam_1 @ (k2_tarski @ X9 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.53/0.75      inference('demod', [status(thm)], ['0', '1'])).
% 0.53/0.75  thf(t22_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.53/0.75  thf('9', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i]:
% 0.53/0.75         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.53/0.75      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.53/0.75  thf('10', plain,
% 0.53/0.75      (![X15 : $i, X16 : $i]:
% 0.53/0.75         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i]:
% 0.53/0.75         ((k2_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))) = (X7))),
% 0.53/0.75      inference('demod', [status(thm)], ['9', '10'])).
% 0.53/0.75  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['8', '11'])).
% 0.53/0.75  thf(commutativity_k2_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.53/0.75  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.75  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.53/0.75      inference('demod', [status(thm)], ['7', '14', '15'])).
% 0.53/0.75  thf(t25_relat_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( v1_relat_1 @ A ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( v1_relat_1 @ B ) =>
% 0.53/0.75           ( ( r1_tarski @ A @ B ) =>
% 0.53/0.75             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.53/0.75               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      (![X22 : $i, X23 : $i]:
% 0.53/0.75         (~ (v1_relat_1 @ X22)
% 0.53/0.75          | (r1_tarski @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22))
% 0.53/0.75          | ~ (r1_tarski @ X23 @ X22)
% 0.53/0.75          | ~ (v1_relat_1 @ X23))),
% 0.53/0.75      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.53/0.75  thf('18', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.53/0.75          | (r1_tarski @ 
% 0.53/0.75             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.53/0.75             (k2_relat_1 @ X0))
% 0.53/0.75          | ~ (v1_relat_1 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['16', '17'])).
% 0.53/0.75  thf('19', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.53/0.75      inference('demod', [status(thm)], ['7', '14', '15'])).
% 0.53/0.75  thf(t3_subset, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.75  thf('20', plain,
% 0.53/0.75      (![X17 : $i, X19 : $i]:
% 0.53/0.75         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.75  thf('21', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.53/0.75          (k1_zfmisc_1 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['19', '20'])).
% 0.53/0.75  thf(cc2_relat_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( v1_relat_1 @ A ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.75  thf('22', plain,
% 0.53/0.75      (![X20 : $i, X21 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.53/0.75          | (v1_relat_1 @ X20)
% 0.53/0.75          | ~ (v1_relat_1 @ X21))),
% 0.53/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.75  thf('23', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (v1_relat_1 @ X0)
% 0.53/0.75          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (v1_relat_1 @ X0)
% 0.53/0.75          | (r1_tarski @ 
% 0.53/0.75             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.53/0.75             (k2_relat_1 @ X0)))),
% 0.53/0.75      inference('clc', [status(thm)], ['18', '23'])).
% 0.53/0.75  thf(t17_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.75  thf('25', plain,
% 0.53/0.75      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.53/0.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.75  thf('26', plain,
% 0.53/0.75      (![X15 : $i, X16 : $i]:
% 0.53/0.75         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.53/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.76  thf('27', plain,
% 0.53/0.76      (![X2 : $i, X3 : $i]:
% 0.53/0.76         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3)) @ X2)),
% 0.53/0.76      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.76  thf('28', plain,
% 0.53/0.76      (![X17 : $i, X19 : $i]:
% 0.53/0.76         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.53/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.76  thf('29', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.53/0.76          (k1_zfmisc_1 @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.76  thf('30', plain,
% 0.53/0.76      (![X20 : $i, X21 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.53/0.76          | (v1_relat_1 @ X20)
% 0.53/0.76          | ~ (v1_relat_1 @ X21))),
% 0.53/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.76  thf('31', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (~ (v1_relat_1 @ X0)
% 0.53/0.76          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.76  thf('32', plain,
% 0.53/0.76      (![X2 : $i, X3 : $i]:
% 0.53/0.76         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3)) @ X2)),
% 0.53/0.76      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.76  thf('33', plain,
% 0.53/0.76      (![X22 : $i, X23 : $i]:
% 0.53/0.76         (~ (v1_relat_1 @ X22)
% 0.53/0.76          | (r1_tarski @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22))
% 0.53/0.76          | ~ (r1_tarski @ X23 @ X22)
% 0.53/0.76          | ~ (v1_relat_1 @ X23))),
% 0.53/0.76      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.53/0.76  thf('34', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.53/0.76          | (r1_tarski @ 
% 0.53/0.76             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.53/0.76             (k2_relat_1 @ X0))
% 0.53/0.76          | ~ (v1_relat_1 @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['32', '33'])).
% 0.53/0.76  thf('35', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (~ (v1_relat_1 @ X1)
% 0.53/0.76          | ~ (v1_relat_1 @ X1)
% 0.53/0.76          | (r1_tarski @ 
% 0.53/0.76             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.53/0.76             (k2_relat_1 @ X1)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['31', '34'])).
% 0.53/0.76  thf('36', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((r1_tarski @ (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.53/0.76           (k2_relat_1 @ X1))
% 0.53/0.76          | ~ (v1_relat_1 @ X1))),
% 0.53/0.76      inference('simplify', [status(thm)], ['35'])).
% 0.53/0.76  thf(t19_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.53/0.76       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.53/0.76  thf('37', plain,
% 0.53/0.76      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.76         (~ (r1_tarski @ X4 @ X5)
% 0.53/0.76          | ~ (r1_tarski @ X4 @ X6)
% 0.53/0.76          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.53/0.76  thf('38', plain,
% 0.53/0.76      (![X15 : $i, X16 : $i]:
% 0.53/0.76         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.53/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.76  thf('39', plain,
% 0.53/0.76      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.76         (~ (r1_tarski @ X4 @ X5)
% 0.53/0.76          | ~ (r1_tarski @ X4 @ X6)
% 0.53/0.76          | (r1_tarski @ X4 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 0.53/0.76      inference('demod', [status(thm)], ['37', '38'])).
% 0.53/0.76  thf('40', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.76         (~ (v1_relat_1 @ X0)
% 0.53/0.76          | (r1_tarski @ 
% 0.53/0.76             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.53/0.76             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.53/0.76          | ~ (r1_tarski @ 
% 0.53/0.76               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.53/0.76      inference('sup-', [status(thm)], ['36', '39'])).
% 0.53/0.76  thf('41', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (~ (v1_relat_1 @ X0)
% 0.53/0.76          | (r1_tarski @ 
% 0.53/0.76             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.53/0.76             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.53/0.76          | ~ (v1_relat_1 @ X1))),
% 0.53/0.76      inference('sup-', [status(thm)], ['24', '40'])).
% 0.53/0.76  thf(t27_relat_1, conjecture,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( v1_relat_1 @ A ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( v1_relat_1 @ B ) =>
% 0.53/0.76           ( r1_tarski @
% 0.53/0.76             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.53/0.76             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.53/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.76    (~( ![A:$i]:
% 0.53/0.76        ( ( v1_relat_1 @ A ) =>
% 0.53/0.76          ( ![B:$i]:
% 0.53/0.76            ( ( v1_relat_1 @ B ) =>
% 0.53/0.76              ( r1_tarski @
% 0.53/0.76                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.53/0.76                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.53/0.76    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.53/0.76  thf('42', plain,
% 0.53/0.76      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.53/0.76          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('43', plain,
% 0.53/0.76      (![X15 : $i, X16 : $i]:
% 0.53/0.76         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.53/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.76  thf('44', plain,
% 0.53/0.76      (![X15 : $i, X16 : $i]:
% 0.53/0.76         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.53/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.76  thf('45', plain,
% 0.53/0.76      (~ (r1_tarski @ 
% 0.53/0.76          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.53/0.76          (k1_setfam_1 @ 
% 0.53/0.76           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.53/0.76      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.53/0.76  thf('46', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.53/0.76      inference('sup-', [status(thm)], ['41', '45'])).
% 0.53/0.76  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('49', plain, ($false),
% 0.53/0.76      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.53/0.76  
% 0.53/0.76  % SZS output end Refutation
% 0.53/0.76  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
