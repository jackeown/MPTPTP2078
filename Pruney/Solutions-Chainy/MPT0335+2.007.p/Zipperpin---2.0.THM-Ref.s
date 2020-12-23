%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XWTfGrExL3

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:13 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 122 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  587 (1060 expanded)
%              Number of equality atoms :   64 ( 118 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ ( k3_xboole_0 @ X25 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    r2_hidden @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X37: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ X39 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X37: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ X39 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('34',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r2_hidden @ X37 @ X38 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_D_2 @ ( k3_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_D_2 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_D_2 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_2 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_tarski @ sk_D_2 )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ sk_D_2 @ ( k1_tarski @ sk_D_2 ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X37: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ X39 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('51',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ ( k1_tarski @ sk_D_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ ( k1_tarski @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('54',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('55',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ k1_xboole_0 )
    = ( k1_tarski @ sk_D_2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_tarski @ sk_D_2 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['25','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = ( k1_tarski @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','17','18','56'])).

thf('58',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D_2 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XWTfGrExL3
% 0.13/0.37  % Computer   : n007.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:22:51 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 845 iterations in 0.401s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.69/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.89  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.69/0.89  thf(t148_zfmisc_1, conjecture,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89     ( ( ( r1_tarski @ A @ B ) & 
% 0.69/0.89         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.69/0.89         ( r2_hidden @ D @ A ) ) =>
% 0.69/0.89       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89        ( ( ( r1_tarski @ A @ B ) & 
% 0.69/0.89            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.69/0.89            ( r2_hidden @ D @ A ) ) =>
% 0.69/0.89          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.69/0.89  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_2))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t50_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.69/0.89       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.69/0.89  thf('1', plain,
% 0.69/0.89      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X27))
% 0.69/0.89           = (k4_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.69/0.89              (k3_xboole_0 @ X25 @ X27)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.69/0.89  thf(t49_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.69/0.89       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.69/0.89  thf('2', plain,
% 0.69/0.89      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.69/0.89           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.69/0.89      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.69/0.89  thf('3', plain,
% 0.69/0.89      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X27))
% 0.69/0.89           = (k3_xboole_0 @ X25 @ 
% 0.69/0.89              (k4_xboole_0 @ X26 @ (k3_xboole_0 @ X25 @ X27))))),
% 0.69/0.89      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.89  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t28_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.69/0.89  thf('5', plain,
% 0.69/0.89      (![X16 : $i, X17 : $i]:
% 0.69/0.89         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.69/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.69/0.89  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.69/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.69/0.89  thf('7', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.89  thf('8', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['6', '7'])).
% 0.69/0.89  thf('9', plain,
% 0.69/0.89      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.69/0.89           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.69/0.89      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.69/0.89           = (k4_xboole_0 @ sk_A @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['8', '9'])).
% 0.69/0.89  thf('11', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.69/0.89           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['3', '10'])).
% 0.69/0.89  thf('12', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.69/0.89           = (k4_xboole_0 @ sk_A @ X0))),
% 0.69/0.89      inference('sup+', [status(thm)], ['8', '9'])).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ sk_A @ X0)
% 0.69/0.89           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['11', '12'])).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      (((k4_xboole_0 @ sk_A @ sk_C_1)
% 0.69/0.89         = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['0', '13'])).
% 0.69/0.89  thf(t48_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.89  thf('15', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.89           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.89  thf('16', plain,
% 0.69/0.89      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.69/0.89         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['14', '15'])).
% 0.69/0.89  thf('17', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.89           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.89  thf('18', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.89  thf('19', plain, ((r2_hidden @ sk_D_2 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(l35_zfmisc_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.89       ( r2_hidden @ A @ B ) ))).
% 0.69/0.89  thf('20', plain,
% 0.69/0.89      (![X37 : $i, X39 : $i]:
% 0.69/0.89         (((k4_xboole_0 @ (k1_tarski @ X37) @ X39) = (k1_xboole_0))
% 0.69/0.89          | ~ (r2_hidden @ X37 @ X39))),
% 0.69/0.89      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_D_2) @ sk_A) = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.89           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_D_2) @ k1_xboole_0)
% 0.69/0.89         = (k3_xboole_0 @ (k1_tarski @ sk_D_2) @ sk_A))),
% 0.69/0.89      inference('sup+', [status(thm)], ['21', '22'])).
% 0.69/0.89  thf('24', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.89  thf('25', plain,
% 0.69/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_D_2) @ k1_xboole_0)
% 0.69/0.89         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('demod', [status(thm)], ['23', '24'])).
% 0.69/0.89  thf('26', plain, ((r2_hidden @ sk_D_2 @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('27', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(d3_tarski, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.69/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.69/0.89  thf('28', plain,
% 0.69/0.89      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X2 @ X3)
% 0.69/0.89          | (r2_hidden @ X2 @ X4)
% 0.69/0.89          | ~ (r1_tarski @ X3 @ X4))),
% 0.69/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.89  thf('30', plain, ((r2_hidden @ sk_D_2 @ sk_B)),
% 0.69/0.89      inference('sup-', [status(thm)], ['26', '29'])).
% 0.69/0.89  thf('31', plain,
% 0.69/0.89      (![X37 : $i, X39 : $i]:
% 0.69/0.89         (((k4_xboole_0 @ (k1_tarski @ X37) @ X39) = (k1_xboole_0))
% 0.69/0.89          | ~ (r2_hidden @ X37 @ X39))),
% 0.69/0.89      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.69/0.89  thf('32', plain,
% 0.69/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_D_2) @ sk_B) = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.89  thf(t47_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.69/0.89  thf('33', plain,
% 0.69/0.89      (![X18 : $i, X19 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.69/0.89           = (k4_xboole_0 @ X18 @ X19))),
% 0.69/0.89      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.69/0.89  thf('34', plain,
% 0.69/0.89      (![X37 : $i, X38 : $i]:
% 0.69/0.89         ((r2_hidden @ X37 @ X38)
% 0.69/0.89          | ((k4_xboole_0 @ (k1_tarski @ X37) @ X38) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) != (k1_xboole_0))
% 0.69/0.89          | (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.89  thf('36', plain,
% 0.69/0.89      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89        | (r2_hidden @ sk_D_2 @ (k3_xboole_0 @ (k1_tarski @ sk_D_2) @ sk_B)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['32', '35'])).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.89  thf('38', plain,
% 0.69/0.89      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.89        | (r2_hidden @ sk_D_2 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_2))))),
% 0.69/0.89      inference('demod', [status(thm)], ['36', '37'])).
% 0.69/0.89  thf('39', plain,
% 0.69/0.89      ((r2_hidden @ sk_D_2 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['38'])).
% 0.69/0.89  thf('40', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_2))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('41', plain,
% 0.69/0.89      (![X18 : $i, X19 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 0.69/0.89           = (k4_xboole_0 @ X18 @ X19))),
% 0.69/0.89      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.69/0.89  thf('42', plain,
% 0.69/0.89      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_2))
% 0.69/0.89         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.69/0.89      inference('sup+', [status(thm)], ['40', '41'])).
% 0.69/0.89  thf('43', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.89           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.89  thf('44', plain,
% 0.69/0.89      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.69/0.89         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['42', '43'])).
% 0.69/0.89  thf('45', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.89           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.89  thf('46', plain,
% 0.69/0.89      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 0.69/0.89         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('demod', [status(thm)], ['44', '45'])).
% 0.69/0.89  thf('47', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_2))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('48', plain,
% 0.69/0.89      (((k1_tarski @ sk_D_2) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('demod', [status(thm)], ['46', '47'])).
% 0.69/0.89  thf('49', plain, ((r2_hidden @ sk_D_2 @ (k1_tarski @ sk_D_2))),
% 0.69/0.89      inference('demod', [status(thm)], ['39', '48'])).
% 0.69/0.89  thf('50', plain,
% 0.69/0.89      (![X37 : $i, X39 : $i]:
% 0.69/0.89         (((k4_xboole_0 @ (k1_tarski @ X37) @ X39) = (k1_xboole_0))
% 0.69/0.89          | ~ (r2_hidden @ X37 @ X39))),
% 0.69/0.89      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.69/0.89  thf('51', plain,
% 0.69/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_D_2) @ (k1_tarski @ sk_D_2))
% 0.69/0.89         = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      (![X20 : $i, X21 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.89           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_D_2) @ k1_xboole_0)
% 0.69/0.89         = (k3_xboole_0 @ (k1_tarski @ sk_D_2) @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['51', '52'])).
% 0.69/0.89  thf(idempotence_k3_xboole_0, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.69/0.89  thf('54', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 0.69/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.69/0.89  thf('55', plain,
% 0.69/0.89      (((k4_xboole_0 @ (k1_tarski @ sk_D_2) @ k1_xboole_0)
% 0.69/0.89         = (k1_tarski @ sk_D_2))),
% 0.69/0.89      inference('demod', [status(thm)], ['53', '54'])).
% 0.69/0.89  thf('56', plain,
% 0.69/0.89      (((k1_tarski @ sk_D_2) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_2)))),
% 0.69/0.89      inference('demod', [status(thm)], ['25', '55'])).
% 0.69/0.89  thf('57', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_tarski @ sk_D_2))),
% 0.69/0.89      inference('demod', [status(thm)], ['16', '17', '18', '56'])).
% 0.69/0.89  thf('58', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_2))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('59', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.89  thf('60', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D_2))),
% 0.69/0.89      inference('demod', [status(thm)], ['58', '59'])).
% 0.69/0.89  thf('61', plain, ($false),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['57', '60'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
