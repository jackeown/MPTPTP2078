%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PhjU1vHcCL

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:12 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 157 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  544 (1396 expanded)
%              Number of equality atoms :   15 (  72 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t50_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( v1_relat_1 @ D )
                 => ( ( ( r1_tarski @ A @ B )
                      & ( r1_tarski @ C @ D ) )
                   => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k5_relat_1 @ X18 @ X19 ) @ ( k5_relat_1 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41','42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PhjU1vHcCL
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:20:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.97/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.97/1.16  % Solved by: fo/fo7.sh
% 0.97/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.16  % done 836 iterations in 0.707s
% 0.97/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.97/1.16  % SZS output start Refutation
% 0.97/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.97/1.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.97/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.97/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.97/1.16  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.97/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.16  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.97/1.16  thf(commutativity_k2_tarski, axiom,
% 0.97/1.16    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.97/1.16  thf('0', plain,
% 0.97/1.16      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.97/1.16      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.97/1.16  thf(t12_setfam_1, axiom,
% 0.97/1.16    (![A:$i,B:$i]:
% 0.97/1.16     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.97/1.16  thf('1', plain,
% 0.97/1.16      (![X12 : $i, X13 : $i]:
% 0.97/1.16         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.97/1.16      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.97/1.16  thf('2', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.16      inference('sup+', [status(thm)], ['0', '1'])).
% 0.97/1.16  thf('3', plain,
% 0.97/1.16      (![X12 : $i, X13 : $i]:
% 0.97/1.16         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.97/1.16      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.97/1.16  thf('4', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.16      inference('sup+', [status(thm)], ['2', '3'])).
% 0.97/1.16  thf(fc1_relat_1, axiom,
% 0.97/1.16    (![A:$i,B:$i]:
% 0.97/1.16     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.97/1.16  thf('5', plain,
% 0.97/1.16      (![X14 : $i, X15 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.97/1.16      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.97/1.16  thf(t17_xboole_1, axiom,
% 0.97/1.16    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.97/1.16  thf('6', plain,
% 0.97/1.16      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.97/1.16      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.97/1.16  thf(d10_xboole_0, axiom,
% 0.97/1.16    (![A:$i,B:$i]:
% 0.97/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.97/1.16  thf('7', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.97/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.16  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.97/1.16      inference('simplify', [status(thm)], ['7'])).
% 0.97/1.16  thf(t19_xboole_1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.97/1.16       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.97/1.16  thf('9', plain,
% 0.97/1.16      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.97/1.16         (~ (r1_tarski @ X5 @ X6)
% 0.97/1.16          | ~ (r1_tarski @ X5 @ X7)
% 0.97/1.16          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.97/1.16      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.97/1.16  thf('10', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.97/1.16      inference('sup-', [status(thm)], ['8', '9'])).
% 0.97/1.16  thf('11', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ 
% 0.97/1.16          (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['6', '10'])).
% 0.97/1.16  thf('12', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.16      inference('sup+', [status(thm)], ['2', '3'])).
% 0.97/1.16  thf('13', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ 
% 0.97/1.16          (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.97/1.16      inference('demod', [status(thm)], ['11', '12'])).
% 0.97/1.16  thf('14', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.16      inference('sup+', [status(thm)], ['2', '3'])).
% 0.97/1.16  thf('15', plain,
% 0.97/1.16      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.97/1.16      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.97/1.16  thf('16', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.97/1.16      inference('sup+', [status(thm)], ['14', '15'])).
% 0.97/1.16  thf('17', plain,
% 0.97/1.16      (![X0 : $i, X2 : $i]:
% 0.97/1.16         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.97/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.16  thf('18', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.97/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['16', '17'])).
% 0.97/1.16  thf('19', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         ((k3_xboole_0 @ X1 @ X0)
% 0.97/1.16           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['13', '18'])).
% 0.97/1.16  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.97/1.16      inference('simplify', [status(thm)], ['7'])).
% 0.97/1.16  thf('21', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.16      inference('sup+', [status(thm)], ['2', '3'])).
% 0.97/1.16  thf('22', plain,
% 0.97/1.16      (![X14 : $i, X15 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.97/1.16      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.97/1.16  thf('23', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.97/1.16      inference('sup+', [status(thm)], ['21', '22'])).
% 0.97/1.16  thf('24', plain,
% 0.97/1.16      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.97/1.16      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.97/1.16  thf(t50_relat_1, axiom,
% 0.97/1.16    (![A:$i]:
% 0.97/1.16     ( ( v1_relat_1 @ A ) =>
% 0.97/1.16       ( ![B:$i]:
% 0.97/1.16         ( ( v1_relat_1 @ B ) =>
% 0.97/1.16           ( ![C:$i]:
% 0.97/1.16             ( ( v1_relat_1 @ C ) =>
% 0.97/1.16               ( ![D:$i]:
% 0.97/1.16                 ( ( v1_relat_1 @ D ) =>
% 0.97/1.16                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.97/1.16                     ( r1_tarski @
% 0.97/1.16                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.97/1.16  thf('25', plain,
% 0.97/1.16      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X16)
% 0.97/1.16          | ~ (v1_relat_1 @ X17)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X18 @ X19) @ (k5_relat_1 @ X16 @ X17))
% 0.97/1.16          | ~ (r1_tarski @ X19 @ X17)
% 0.97/1.16          | ~ (r1_tarski @ X18 @ X16)
% 0.97/1.16          | ~ (v1_relat_1 @ X19)
% 0.97/1.16          | ~ (v1_relat_1 @ X18))),
% 0.97/1.16      inference('cnf', [status(esa)], [t50_relat_1])).
% 0.97/1.16  thf('26', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X2)
% 0.97/1.16          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.97/1.16          | ~ (r1_tarski @ X2 @ X3)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.97/1.16             (k5_relat_1 @ X3 @ X0))
% 0.97/1.16          | ~ (v1_relat_1 @ X0)
% 0.97/1.16          | ~ (v1_relat_1 @ X3))),
% 0.97/1.16      inference('sup-', [status(thm)], ['24', '25'])).
% 0.97/1.16  thf('27', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X0)
% 0.97/1.16          | ~ (v1_relat_1 @ X2)
% 0.97/1.16          | ~ (v1_relat_1 @ X1)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X3 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.97/1.16             (k5_relat_1 @ X2 @ X1))
% 0.97/1.16          | ~ (r1_tarski @ X3 @ X2)
% 0.97/1.16          | ~ (v1_relat_1 @ X3))),
% 0.97/1.16      inference('sup-', [status(thm)], ['23', '26'])).
% 0.97/1.16  thf('28', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X0)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 0.97/1.16             (k5_relat_1 @ X0 @ X1))
% 0.97/1.16          | ~ (v1_relat_1 @ X1)
% 0.97/1.16          | ~ (v1_relat_1 @ X0)
% 0.97/1.16          | ~ (v1_relat_1 @ X2))),
% 0.97/1.16      inference('sup-', [status(thm)], ['20', '27'])).
% 0.97/1.16  thf('29', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X2)
% 0.97/1.16          | ~ (v1_relat_1 @ X1)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 0.97/1.16             (k5_relat_1 @ X0 @ X1))
% 0.97/1.16          | ~ (v1_relat_1 @ X0))),
% 0.97/1.16      inference('simplify', [status(thm)], ['28'])).
% 0.97/1.16  thf('30', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.97/1.16           (k5_relat_1 @ X2 @ X1))
% 0.97/1.16          | ~ (v1_relat_1 @ X2)
% 0.97/1.16          | ~ (v1_relat_1 @ X1)
% 0.97/1.16          | ~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.97/1.16      inference('sup+', [status(thm)], ['19', '29'])).
% 0.97/1.16  thf('31', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X1)
% 0.97/1.16          | ~ (v1_relat_1 @ X1)
% 0.97/1.16          | ~ (v1_relat_1 @ X2)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.97/1.16             (k5_relat_1 @ X2 @ X1)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['5', '30'])).
% 0.97/1.16  thf('32', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.97/1.16           (k5_relat_1 @ X2 @ X1))
% 0.97/1.16          | ~ (v1_relat_1 @ X2)
% 0.97/1.16          | ~ (v1_relat_1 @ X1))),
% 0.97/1.16      inference('simplify', [status(thm)], ['31'])).
% 0.97/1.16  thf('33', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.97/1.16           (k5_relat_1 @ X2 @ X0))
% 0.97/1.16          | ~ (v1_relat_1 @ X0)
% 0.97/1.16          | ~ (v1_relat_1 @ X2))),
% 0.97/1.16      inference('sup+', [status(thm)], ['4', '32'])).
% 0.97/1.16  thf('34', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.97/1.16           (k5_relat_1 @ X2 @ X1))
% 0.97/1.16          | ~ (v1_relat_1 @ X2)
% 0.97/1.16          | ~ (v1_relat_1 @ X1))),
% 0.97/1.16      inference('simplify', [status(thm)], ['31'])).
% 0.97/1.16  thf('35', plain,
% 0.97/1.16      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.97/1.16         (~ (r1_tarski @ X5 @ X6)
% 0.97/1.16          | ~ (r1_tarski @ X5 @ X7)
% 0.97/1.16          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.97/1.16      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.97/1.16  thf('36', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X0)
% 0.97/1.16          | ~ (v1_relat_1 @ X1)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 0.97/1.16             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 0.97/1.16          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 0.97/1.16      inference('sup-', [status(thm)], ['34', '35'])).
% 0.97/1.16  thf('37', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X1)
% 0.97/1.16          | ~ (v1_relat_1 @ X0)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 0.97/1.16             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 0.97/1.16          | ~ (v1_relat_1 @ X1)
% 0.97/1.16          | ~ (v1_relat_1 @ X2))),
% 0.97/1.16      inference('sup-', [status(thm)], ['33', '36'])).
% 0.97/1.16  thf('38', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X2)
% 0.97/1.16          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 0.97/1.16             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 0.97/1.16          | ~ (v1_relat_1 @ X0)
% 0.97/1.16          | ~ (v1_relat_1 @ X1))),
% 0.97/1.16      inference('simplify', [status(thm)], ['37'])).
% 0.97/1.16  thf(t52_relat_1, conjecture,
% 0.97/1.16    (![A:$i]:
% 0.97/1.16     ( ( v1_relat_1 @ A ) =>
% 0.97/1.16       ( ![B:$i]:
% 0.97/1.16         ( ( v1_relat_1 @ B ) =>
% 0.97/1.16           ( ![C:$i]:
% 0.97/1.16             ( ( v1_relat_1 @ C ) =>
% 0.97/1.16               ( r1_tarski @
% 0.97/1.16                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 0.97/1.16                 ( k3_xboole_0 @
% 0.97/1.16                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.97/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.16    (~( ![A:$i]:
% 0.97/1.16        ( ( v1_relat_1 @ A ) =>
% 0.97/1.16          ( ![B:$i]:
% 0.97/1.16            ( ( v1_relat_1 @ B ) =>
% 0.97/1.16              ( ![C:$i]:
% 0.97/1.16                ( ( v1_relat_1 @ C ) =>
% 0.97/1.16                  ( r1_tarski @
% 0.97/1.16                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 0.97/1.16                    ( k3_xboole_0 @
% 0.97/1.16                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 0.97/1.16    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 0.97/1.16  thf('39', plain,
% 0.97/1.16      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 0.97/1.16          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 0.97/1.16           (k5_relat_1 @ sk_A @ sk_C)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('40', plain,
% 0.97/1.16      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 0.97/1.16      inference('sup-', [status(thm)], ['38', '39'])).
% 0.97/1.16  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('44', plain, ($false),
% 0.97/1.16      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.97/1.16  
% 0.97/1.16  % SZS output end Refutation
% 0.97/1.16  
% 0.97/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
