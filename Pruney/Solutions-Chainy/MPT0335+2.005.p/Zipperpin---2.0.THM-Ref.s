%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AL96u507aE

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:13 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   63 (  99 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  440 ( 807 expanded)
%              Number of equality atoms :   48 (  89 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k3_xboole_0 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k3_xboole_0 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k3_xboole_0 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['13','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','38'])).

thf('40',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_2 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ( k3_xboole_0 @ sk_C_2 @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AL96u507aE
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:24:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.05  % Solved by: fo/fo7.sh
% 0.84/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.05  % done 1276 iterations in 0.576s
% 0.84/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.05  % SZS output start Refutation
% 0.84/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.05  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.84/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.84/1.05  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.84/1.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.05  thf(t148_zfmisc_1, conjecture,
% 0.84/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.05     ( ( ( r1_tarski @ A @ B ) & 
% 0.84/1.05         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.84/1.05         ( r2_hidden @ D @ A ) ) =>
% 0.84/1.05       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.84/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.05    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.05        ( ( ( r1_tarski @ A @ B ) & 
% 0.84/1.05            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.84/1.05            ( r2_hidden @ D @ A ) ) =>
% 0.84/1.05          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.84/1.05    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.84/1.05  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(d3_tarski, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( r1_tarski @ A @ B ) <=>
% 0.84/1.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.84/1.05  thf('1', plain,
% 0.84/1.05      (![X3 : $i, X5 : $i]:
% 0.84/1.05         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.05  thf(d1_tarski, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.84/1.05       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.84/1.05  thf('2', plain,
% 0.84/1.05      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X28 @ X27)
% 0.84/1.05          | ((X28) = (X25))
% 0.84/1.05          | ((X27) != (k1_tarski @ X25)))),
% 0.84/1.05      inference('cnf', [status(esa)], [d1_tarski])).
% 0.84/1.05  thf('3', plain,
% 0.84/1.05      (![X25 : $i, X28 : $i]:
% 0.84/1.05         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['2'])).
% 0.84/1.05  thf('4', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.84/1.05          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['1', '3'])).
% 0.84/1.05  thf('5', plain,
% 0.84/1.05      (![X3 : $i, X5 : $i]:
% 0.84/1.05         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.05  thf('6', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ X1)
% 0.84/1.05          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.84/1.05          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.84/1.05  thf('7', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.84/1.05      inference('simplify', [status(thm)], ['6'])).
% 0.84/1.05  thf('8', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_A)),
% 0.84/1.05      inference('sup-', [status(thm)], ['0', '7'])).
% 0.84/1.05  thf(t28_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.84/1.05  thf('9', plain,
% 0.84/1.05      (![X19 : $i, X20 : $i]:
% 0.84/1.05         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.84/1.05      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.05  thf('10', plain,
% 0.84/1.05      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['8', '9'])).
% 0.84/1.05  thf(commutativity_k3_xboole_0, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.84/1.05  thf('11', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.05  thf('12', plain,
% 0.84/1.05      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['10', '11'])).
% 0.84/1.05  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_tarski @ sk_D_1))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('14', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.05  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('16', plain,
% 0.84/1.05      (![X19 : $i, X20 : $i]:
% 0.84/1.05         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.84/1.05      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.05  thf('17', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.05  thf('18', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.05  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['17', '18'])).
% 0.84/1.05  thf(t16_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.84/1.05       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.84/1.05  thf('20', plain,
% 0.84/1.05      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18)
% 0.84/1.05           = (k3_xboole_0 @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.84/1.05  thf('21', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ sk_A @ X0)
% 0.84/1.05           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['19', '20'])).
% 0.84/1.05  thf('22', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.05  thf(t47_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('23', plain,
% 0.84/1.05      (![X21 : $i, X22 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 0.84/1.05           = (k4_xboole_0 @ X21 @ X22))),
% 0.84/1.05      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.84/1.05  thf('24', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.84/1.05           = (k4_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['22', '23'])).
% 0.84/1.05  thf(t48_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('25', plain,
% 0.84/1.05      (![X23 : $i, X24 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.84/1.05           = (k3_xboole_0 @ X23 @ X24))),
% 0.84/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.84/1.05  thf('26', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.84/1.05           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['24', '25'])).
% 0.84/1.05  thf('27', plain,
% 0.84/1.05      (![X23 : $i, X24 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.84/1.05           = (k3_xboole_0 @ X23 @ X24))),
% 0.84/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.84/1.05  thf('28', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ X1 @ X0)
% 0.84/1.05           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.05  thf('29', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.84/1.05           = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.84/1.05              (k3_xboole_0 @ sk_A @ X0)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['21', '28'])).
% 0.84/1.05  thf('30', plain,
% 0.84/1.05      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18)
% 0.84/1.05           = (k3_xboole_0 @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.84/1.05  thf('31', plain,
% 0.84/1.05      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18)
% 0.84/1.05           = (k3_xboole_0 @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.84/1.05  thf('32', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ X1 @ X0)
% 0.84/1.05           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.05  thf('33', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ X1 @ X0)
% 0.84/1.05           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.05  thf('34', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 0.84/1.05           = (k3_xboole_0 @ sk_A @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.84/1.05  thf('35', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.84/1.05           = (k3_xboole_0 @ sk_A @ X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['14', '34'])).
% 0.84/1.05  thf('36', plain,
% 0.84/1.05      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.84/1.05         = (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.84/1.05      inference('sup+', [status(thm)], ['13', '35'])).
% 0.84/1.05  thf('37', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.05  thf('38', plain,
% 0.84/1.05      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.84/1.05         = (k3_xboole_0 @ sk_C_2 @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['36', '37'])).
% 0.84/1.05  thf('39', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_2 @ sk_A))),
% 0.84/1.05      inference('sup+', [status(thm)], ['12', '38'])).
% 0.84/1.05  thf('40', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) != (k1_tarski @ sk_D_1))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.05  thf('42', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) != (k1_tarski @ sk_D_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['40', '41'])).
% 0.84/1.05  thf('43', plain, ($false),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['39', '42'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
