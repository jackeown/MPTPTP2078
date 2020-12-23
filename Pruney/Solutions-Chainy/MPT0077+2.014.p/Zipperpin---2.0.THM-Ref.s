%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p7h1FvTfY1

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:51 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 291 expanded)
%              Number of leaves         :   19 (  88 expanded)
%              Depth                    :   20
%              Number of atoms          :  593 (2935 expanded)
%              Number of equality atoms :   33 (  59 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 )
      | ( r1_xboole_0 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 )
      | ( r1_xboole_0 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['28'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('40',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','25','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','40'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['27','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p7h1FvTfY1
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:41:18 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.35  % Running in FO mode
% 0.77/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.93  % Solved by: fo/fo7.sh
% 0.77/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.93  % done 1380 iterations in 0.474s
% 0.77/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.93  % SZS output start Refutation
% 0.77/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.93  thf(t70_xboole_1, conjecture,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.77/0.93            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.77/0.93       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.77/0.93            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.77/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.93        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.77/0.93               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.77/0.93          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.77/0.93               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.77/0.93    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.77/0.93  thf('0', plain,
% 0.77/0.93      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 0.77/0.93        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.77/0.93        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('1', plain,
% 0.77/0.93      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.77/0.93         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.93      inference('split', [status(esa)], ['0'])).
% 0.77/0.93  thf('2', plain,
% 0.77/0.93      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 0.77/0.93       ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.93      inference('split', [status(esa)], ['0'])).
% 0.77/0.93  thf('3', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.77/0.93        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('4', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.93      inference('split', [status(esa)], ['3'])).
% 0.77/0.93  thf(symmetry_r1_xboole_0, axiom,
% 0.77/0.93    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.77/0.93  thf('5', plain,
% 0.77/0.93      (![X5 : $i, X6 : $i]:
% 0.77/0.93         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.77/0.93      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.77/0.93  thf('6', plain,
% 0.77/0.93      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.93  thf(t7_xboole_1, axiom,
% 0.77/0.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.93  thf('7', plain,
% 0.77/0.93      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.77/0.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.93  thf(t63_xboole_1, axiom,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.77/0.93       ( r1_xboole_0 @ A @ C ) ))).
% 0.77/0.93  thf('8', plain,
% 0.77/0.93      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/0.93         (~ (r1_tarski @ X25 @ X26)
% 0.77/0.93          | ~ (r1_xboole_0 @ X26 @ X27)
% 0.77/0.93          | (r1_xboole_0 @ X25 @ X27))),
% 0.77/0.93      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.77/0.93  thf('9', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.93         ((r1_xboole_0 @ X1 @ X2)
% 0.77/0.93          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.77/0.93      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.93  thf('10', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_B @ sk_A))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['6', '9'])).
% 0.77/0.93  thf('11', plain,
% 0.77/0.93      (![X5 : $i, X6 : $i]:
% 0.77/0.93         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.77/0.93      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.77/0.93  thf('12', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/0.93  thf('13', plain,
% 0.77/0.93      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.77/0.93      inference('split', [status(esa)], ['0'])).
% 0.77/0.93  thf('14', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.77/0.93       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.93  thf('15', plain,
% 0.77/0.93      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.93  thf(commutativity_k2_xboole_0, axiom,
% 0.77/0.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.77/0.93  thf('16', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.93  thf('17', plain,
% 0.77/0.93      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.77/0.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.93  thf('18', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['16', '17'])).
% 0.77/0.93  thf('19', plain,
% 0.77/0.93      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/0.93         (~ (r1_tarski @ X25 @ X26)
% 0.77/0.93          | ~ (r1_xboole_0 @ X26 @ X27)
% 0.77/0.93          | (r1_xboole_0 @ X25 @ X27))),
% 0.77/0.93      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.77/0.93  thf('20', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.93         ((r1_xboole_0 @ X0 @ X2)
% 0.77/0.93          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.77/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/0.93  thf('21', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_C_1 @ sk_A))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['15', '20'])).
% 0.77/0.93  thf('22', plain,
% 0.77/0.93      (![X5 : $i, X6 : $i]:
% 0.77/0.93         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.77/0.93      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.77/0.93  thf('23', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/0.93  thf('24', plain,
% 0.77/0.93      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.77/0.93      inference('split', [status(esa)], ['0'])).
% 0.77/0.93  thf('25', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.77/0.93       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.93  thf('26', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.77/0.93      inference('sat_resolution*', [status(thm)], ['2', '14', '25'])).
% 0.77/0.93  thf('27', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.77/0.93      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.77/0.93  thf('28', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.77/0.93        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('29', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.77/0.93      inference('split', [status(esa)], ['28'])).
% 0.77/0.93  thf(d7_xboole_0, axiom,
% 0.77/0.93    (![A:$i,B:$i]:
% 0.77/0.93     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.77/0.93       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.93  thf('30', plain,
% 0.77/0.93      (![X2 : $i, X3 : $i]:
% 0.77/0.93         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.77/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.93  thf('31', plain,
% 0.77/0.93      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.93  thf('32', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.77/0.93       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.77/0.93      inference('split', [status(esa)], ['28'])).
% 0.77/0.93  thf('33', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.93      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '32'])).
% 0.77/0.93  thf('34', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.77/0.93      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 0.77/0.93  thf(t40_xboole_1, axiom,
% 0.77/0.93    (![A:$i,B:$i]:
% 0.77/0.93     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.77/0.93  thf('35', plain,
% 0.77/0.93      (![X16 : $i, X17 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.77/0.93           = (k4_xboole_0 @ X16 @ X17))),
% 0.77/0.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.93  thf('36', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.77/0.93      inference('split', [status(esa)], ['3'])).
% 0.77/0.93  thf('37', plain,
% 0.77/0.93      (![X2 : $i, X3 : $i]:
% 0.77/0.93         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.77/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.93  thf('38', plain,
% 0.77/0.93      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.77/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['36', '37'])).
% 0.77/0.93  thf('39', plain,
% 0.77/0.93      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.77/0.93       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.77/0.93      inference('split', [status(esa)], ['3'])).
% 0.77/0.93  thf('40', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.93      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '39'])).
% 0.77/0.93  thf('41', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.77/0.93      inference('simpl_trail', [status(thm)], ['38', '40'])).
% 0.77/0.93  thf(t52_xboole_1, axiom,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.77/0.93       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.77/0.93  thf('42', plain,
% 0.77/0.93      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.77/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ 
% 0.77/0.93              (k3_xboole_0 @ X22 @ X24)))),
% 0.77/0.93      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.77/0.93  thf('43', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.77/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['41', '42'])).
% 0.77/0.93  thf('44', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.93  thf('45', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.93  thf(t1_boole, axiom,
% 0.77/0.93    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/0.93  thf('46', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.77/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.77/0.93  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['45', '46'])).
% 0.77/0.93  thf('48', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.77/0.93           = (k4_xboole_0 @ sk_A @ X0))),
% 0.77/0.93      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.77/0.93  thf('49', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.77/0.93           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.77/0.93      inference('sup+', [status(thm)], ['35', '48'])).
% 0.77/0.93  thf('50', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.77/0.93           = (k4_xboole_0 @ sk_A @ X0))),
% 0.77/0.93      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.77/0.93  thf('51', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ sk_A @ X0)
% 0.77/0.93           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.77/0.93      inference('demod', [status(thm)], ['49', '50'])).
% 0.77/0.93  thf(t48_xboole_1, axiom,
% 0.77/0.93    (![A:$i,B:$i]:
% 0.77/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.93  thf('52', plain,
% 0.77/0.93      (![X18 : $i, X19 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.77/0.93           = (k3_xboole_0 @ X18 @ X19))),
% 0.77/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.93  thf('53', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.77/0.93           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.77/0.93      inference('sup+', [status(thm)], ['51', '52'])).
% 0.77/0.93  thf('54', plain,
% 0.77/0.93      (![X18 : $i, X19 : $i]:
% 0.77/0.93         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.77/0.93           = (k3_xboole_0 @ X18 @ X19))),
% 0.77/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.93  thf('55', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         ((k3_xboole_0 @ sk_A @ X0)
% 0.77/0.93           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.77/0.93      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.93  thf('56', plain,
% 0.77/0.93      (![X2 : $i, X4 : $i]:
% 0.77/0.93         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.77/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.93  thf('57', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.77/0.93          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['55', '56'])).
% 0.77/0.93  thf('58', plain,
% 0.77/0.93      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/0.93        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['34', '57'])).
% 0.77/0.93  thf('59', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.93  thf('60', plain,
% 0.77/0.93      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/0.93        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.77/0.93      inference('demod', [status(thm)], ['58', '59'])).
% 0.77/0.93  thf('61', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.77/0.93      inference('simplify', [status(thm)], ['60'])).
% 0.77/0.93  thf('62', plain, ($false), inference('demod', [status(thm)], ['27', '61'])).
% 0.77/0.93  
% 0.77/0.93  % SZS output end Refutation
% 0.77/0.93  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
