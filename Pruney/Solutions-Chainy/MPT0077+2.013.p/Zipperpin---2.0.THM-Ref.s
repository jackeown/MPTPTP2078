%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZEsLE1Pv91

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:50 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 218 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  584 (2168 expanded)
%              Number of equality atoms :   33 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 )
      | ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 )
      | ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
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
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('39',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['47','49'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','58'])).

thf('60',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['27','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZEsLE1Pv91
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.12/3.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.12/3.32  % Solved by: fo/fo7.sh
% 3.12/3.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.12/3.32  % done 4126 iterations in 2.859s
% 3.12/3.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.12/3.32  % SZS output start Refutation
% 3.12/3.32  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.12/3.32  thf(sk_A_type, type, sk_A: $i).
% 3.12/3.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.12/3.32  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.12/3.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.12/3.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.12/3.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.12/3.32  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.12/3.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.12/3.32  thf(t70_xboole_1, conjecture,
% 3.12/3.32    (![A:$i,B:$i,C:$i]:
% 3.12/3.32     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 3.12/3.32            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 3.12/3.32       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 3.12/3.32            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 3.12/3.32  thf(zf_stmt_0, negated_conjecture,
% 3.12/3.32    (~( ![A:$i,B:$i,C:$i]:
% 3.12/3.32        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 3.12/3.32               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 3.12/3.32          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 3.12/3.32               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 3.12/3.32    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 3.12/3.32  thf('0', plain,
% 3.12/3.32      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 3.12/3.32        | ~ (r1_xboole_0 @ sk_A @ sk_B_1)
% 3.12/3.32        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.32  thf('1', plain,
% 3.12/3.32      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 3.12/3.32         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.32      inference('split', [status(esa)], ['0'])).
% 3.12/3.32  thf('2', plain,
% 3.12/3.32      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))) | 
% 3.12/3.32       ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B_1))),
% 3.12/3.32      inference('split', [status(esa)], ['0'])).
% 3.12/3.32  thf('3', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.12/3.32        | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 3.12/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.32  thf('4', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.32      inference('split', [status(esa)], ['3'])).
% 3.12/3.32  thf(symmetry_r1_xboole_0, axiom,
% 3.12/3.32    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 3.12/3.32  thf('5', plain,
% 3.12/3.32      (![X5 : $i, X6 : $i]:
% 3.12/3.32         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.12/3.32      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.12/3.32  thf('6', plain,
% 3.12/3.32      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.32      inference('sup-', [status(thm)], ['4', '5'])).
% 3.12/3.32  thf(t7_xboole_1, axiom,
% 3.12/3.32    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.12/3.32  thf('7', plain,
% 3.12/3.32      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 3.12/3.32      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.12/3.32  thf(t63_xboole_1, axiom,
% 3.12/3.32    (![A:$i,B:$i,C:$i]:
% 3.12/3.32     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 3.12/3.32       ( r1_xboole_0 @ A @ C ) ))).
% 3.12/3.32  thf('8', plain,
% 3.12/3.32      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.12/3.32         (~ (r1_tarski @ X28 @ X29)
% 3.12/3.32          | ~ (r1_xboole_0 @ X29 @ X30)
% 3.12/3.32          | (r1_xboole_0 @ X28 @ X30))),
% 3.12/3.32      inference('cnf', [status(esa)], [t63_xboole_1])).
% 3.12/3.32  thf('9', plain,
% 3.12/3.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.32         ((r1_xboole_0 @ X1 @ X2)
% 3.12/3.32          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 3.12/3.32      inference('sup-', [status(thm)], ['7', '8'])).
% 3.12/3.32  thf('10', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_B_1 @ sk_A))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.32      inference('sup-', [status(thm)], ['6', '9'])).
% 3.12/3.32  thf('11', plain,
% 3.12/3.32      (![X5 : $i, X6 : $i]:
% 3.12/3.32         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.12/3.32      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.12/3.32  thf('12', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ sk_B_1))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.32      inference('sup-', [status(thm)], ['10', '11'])).
% 3.12/3.32  thf('13', plain,
% 3.12/3.32      ((~ (r1_xboole_0 @ sk_A @ sk_B_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 3.12/3.32      inference('split', [status(esa)], ['0'])).
% 3.12/3.32  thf('14', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 3.12/3.32       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.32      inference('sup-', [status(thm)], ['12', '13'])).
% 3.12/3.32  thf('15', plain,
% 3.12/3.32      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.32      inference('sup-', [status(thm)], ['4', '5'])).
% 3.12/3.32  thf(commutativity_k2_xboole_0, axiom,
% 3.12/3.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.12/3.32  thf('16', plain,
% 3.12/3.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.12/3.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.12/3.32  thf('17', plain,
% 3.12/3.32      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 3.12/3.32      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.12/3.32  thf('18', plain,
% 3.12/3.32      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.12/3.32      inference('sup+', [status(thm)], ['16', '17'])).
% 3.12/3.32  thf('19', plain,
% 3.12/3.32      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.12/3.32         (~ (r1_tarski @ X28 @ X29)
% 3.12/3.32          | ~ (r1_xboole_0 @ X29 @ X30)
% 3.12/3.32          | (r1_xboole_0 @ X28 @ X30))),
% 3.12/3.32      inference('cnf', [status(esa)], [t63_xboole_1])).
% 3.12/3.32  thf('20', plain,
% 3.12/3.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.32         ((r1_xboole_0 @ X0 @ X2)
% 3.12/3.32          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 3.12/3.32      inference('sup-', [status(thm)], ['18', '19'])).
% 3.12/3.32  thf('21', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_C_1 @ sk_A))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.32      inference('sup-', [status(thm)], ['15', '20'])).
% 3.12/3.32  thf('22', plain,
% 3.12/3.32      (![X5 : $i, X6 : $i]:
% 3.12/3.32         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.12/3.32      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.12/3.32  thf('23', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 3.12/3.32      inference('sup-', [status(thm)], ['21', '22'])).
% 3.12/3.32  thf('24', plain,
% 3.12/3.32      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 3.12/3.32      inference('split', [status(esa)], ['0'])).
% 3.12/3.32  thf('25', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 3.12/3.32       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.32      inference('sup-', [status(thm)], ['23', '24'])).
% 3.12/3.32  thf('26', plain,
% 3.12/3.32      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.32      inference('sat_resolution*', [status(thm)], ['2', '14', '25'])).
% 3.12/3.32  thf('27', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.12/3.32      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 3.12/3.32  thf('28', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.12/3.32        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 3.12/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.32  thf('29', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 3.12/3.32      inference('split', [status(esa)], ['28'])).
% 3.12/3.32  thf(d7_xboole_0, axiom,
% 3.12/3.32    (![A:$i,B:$i]:
% 3.12/3.32     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.12/3.32       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.12/3.32  thf('30', plain,
% 3.12/3.32      (![X2 : $i, X3 : $i]:
% 3.12/3.32         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.12/3.32      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.12/3.32  thf('31', plain,
% 3.12/3.32      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 3.12/3.32      inference('sup-', [status(thm)], ['29', '30'])).
% 3.12/3.32  thf('32', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 3.12/3.32       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.32      inference('split', [status(esa)], ['28'])).
% 3.12/3.32  thf('33', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 3.12/3.32      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '32'])).
% 3.12/3.32  thf('34', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 3.12/3.32      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 3.12/3.32  thf('35', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 3.12/3.32      inference('split', [status(esa)], ['3'])).
% 3.12/3.32  thf('36', plain,
% 3.12/3.32      (![X2 : $i, X3 : $i]:
% 3.12/3.32         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.12/3.32      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.12/3.32  thf('37', plain,
% 3.12/3.32      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 3.12/3.32      inference('sup-', [status(thm)], ['35', '36'])).
% 3.12/3.32  thf(t51_xboole_1, axiom,
% 3.12/3.32    (![A:$i,B:$i]:
% 3.12/3.32     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 3.12/3.32       ( A ) ))).
% 3.12/3.32  thf('38', plain,
% 3.12/3.32      (![X26 : $i, X27 : $i]:
% 3.12/3.32         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 3.12/3.32           = (X26))),
% 3.12/3.32      inference('cnf', [status(esa)], [t51_xboole_1])).
% 3.12/3.32  thf('39', plain,
% 3.12/3.32      ((((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A)))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 3.12/3.32      inference('sup+', [status(thm)], ['37', '38'])).
% 3.12/3.32  thf(t3_boole, axiom,
% 3.12/3.32    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.12/3.32  thf('40', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 3.12/3.32      inference('cnf', [status(esa)], [t3_boole])).
% 3.12/3.32  thf(t40_xboole_1, axiom,
% 3.12/3.32    (![A:$i,B:$i]:
% 3.12/3.32     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.12/3.32  thf('41', plain,
% 3.12/3.32      (![X19 : $i, X20 : $i]:
% 3.12/3.32         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 3.12/3.32           = (k4_xboole_0 @ X19 @ X20))),
% 3.12/3.32      inference('cnf', [status(esa)], [t40_xboole_1])).
% 3.12/3.32  thf('42', plain,
% 3.12/3.32      (![X0 : $i]:
% 3.12/3.32         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 3.12/3.32      inference('sup+', [status(thm)], ['40', '41'])).
% 3.12/3.32  thf('43', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 3.12/3.32      inference('cnf', [status(esa)], [t3_boole])).
% 3.12/3.32  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.12/3.32      inference('demod', [status(thm)], ['42', '43'])).
% 3.12/3.32  thf('45', plain,
% 3.12/3.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.12/3.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.12/3.32  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.12/3.32      inference('sup+', [status(thm)], ['44', '45'])).
% 3.12/3.32  thf('47', plain,
% 3.12/3.32      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))
% 3.12/3.32         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 3.12/3.32      inference('demod', [status(thm)], ['39', '46'])).
% 3.12/3.32  thf('48', plain,
% 3.12/3.32      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 3.12/3.32       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.32      inference('split', [status(esa)], ['3'])).
% 3.12/3.32  thf('49', plain, (((r1_xboole_0 @ sk_A @ sk_B_1))),
% 3.12/3.32      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '48'])).
% 3.12/3.32  thf('50', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 3.12/3.32      inference('simpl_trail', [status(thm)], ['47', '49'])).
% 3.12/3.32  thf(t41_xboole_1, axiom,
% 3.12/3.32    (![A:$i,B:$i,C:$i]:
% 3.12/3.32     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.12/3.32       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.12/3.32  thf('51', plain,
% 3.12/3.32      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.12/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 3.12/3.32           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 3.12/3.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.12/3.32  thf(t48_xboole_1, axiom,
% 3.12/3.32    (![A:$i,B:$i]:
% 3.12/3.32     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.12/3.32  thf('52', plain,
% 3.12/3.32      (![X24 : $i, X25 : $i]:
% 3.12/3.32         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 3.12/3.32           = (k3_xboole_0 @ X24 @ X25))),
% 3.12/3.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.12/3.32  thf('53', plain,
% 3.12/3.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.12/3.32         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 3.12/3.32           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.12/3.32      inference('sup+', [status(thm)], ['51', '52'])).
% 3.12/3.32  thf('54', plain,
% 3.12/3.32      (![X0 : $i]:
% 3.12/3.32         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 3.12/3.32           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 3.12/3.32      inference('sup+', [status(thm)], ['50', '53'])).
% 3.12/3.32  thf('55', plain,
% 3.12/3.32      (![X24 : $i, X25 : $i]:
% 3.12/3.32         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 3.12/3.32           = (k3_xboole_0 @ X24 @ X25))),
% 3.12/3.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.12/3.32  thf('56', plain,
% 3.12/3.32      (![X0 : $i]:
% 3.12/3.32         ((k3_xboole_0 @ sk_A @ X0)
% 3.12/3.32           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 3.12/3.32      inference('demod', [status(thm)], ['54', '55'])).
% 3.12/3.32  thf('57', plain,
% 3.12/3.32      (![X2 : $i, X4 : $i]:
% 3.12/3.32         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.12/3.32      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.12/3.32  thf('58', plain,
% 3.12/3.32      (![X0 : $i]:
% 3.12/3.32         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 3.12/3.32          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 3.12/3.32      inference('sup-', [status(thm)], ['56', '57'])).
% 3.12/3.32  thf('59', plain,
% 3.12/3.32      ((((k1_xboole_0) != (k1_xboole_0))
% 3.12/3.32        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 3.12/3.32      inference('sup-', [status(thm)], ['34', '58'])).
% 3.12/3.32  thf('60', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.12/3.32      inference('simplify', [status(thm)], ['59'])).
% 3.12/3.32  thf('61', plain, ($false), inference('demod', [status(thm)], ['27', '60'])).
% 3.12/3.32  
% 3.12/3.32  % SZS output end Refutation
% 3.12/3.32  
% 3.12/3.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
