%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PwAEGhywPH

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:52 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 677 expanded)
%              Number of leaves         :   25 ( 200 expanded)
%              Depth                    :   17
%              Number of atoms          :  962 (6951 expanded)
%              Number of equality atoms :   48 ( 250 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ X37 @ ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ~ ( r1_xboole_0 @ X35 @ X36 )
      | ( r1_xboole_0 @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ X37 @ ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X27 @ X28 ) @ X29 )
      | ~ ( r1_tarski @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
      = k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C_2 ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','38'])).

thf('40',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) )
        = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('52',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_2 @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_2 @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['57','65'])).

thf('67',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('68',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
      = k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('70',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','38','69'])).

thf('71',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('72',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['2','14','38','71'])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['68','70','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('77',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
        | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
        | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','38','69'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C_2 ) )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['73','85'])).

thf('87',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['68','70','72'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['86','87','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['40','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PwAEGhywPH
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 685 iterations in 0.179s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.64  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.64  thf(t70_xboole_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.45/0.64            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.45/0.64       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.45/0.64            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.64        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.45/0.64               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.45/0.64          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.45/0.64               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      ((~ (r1_xboole_0 @ sk_A @ sk_C_2)
% 0.45/0.64        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.45/0.64        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.45/0.64         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) | 
% 0.45/0.64       ~ ((r1_xboole_0 @ sk_A @ sk_C_2)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('split', [status(esa)], ['0'])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.45/0.64        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.45/0.64         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 0.45/0.64      inference('split', [status(esa)], ['3'])).
% 0.45/0.64  thf(symmetry_r1_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A))
% 0.45/0.64         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf(t7_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X37 : $i, X38 : $i]: (r1_tarski @ X37 @ (k2_xboole_0 @ X37 @ X38))),
% 0.45/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.64  thf(t63_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.45/0.64       ( r1_xboole_0 @ A @ C ) ))).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X34 @ X35)
% 0.45/0.64          | ~ (r1_xboole_0 @ X35 @ X36)
% 0.45/0.64          | (r1_xboole_0 @ X34 @ X36))),
% 0.45/0.64      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X1 @ X2)
% 0.45/0.64          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (((r1_xboole_0 @ sk_B @ sk_A))
% 0.45/0.64         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.45/0.65       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('split', [status(esa)], ['3'])).
% 0.45/0.65  thf(d7_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.65       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf(t23_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.45/0.65       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.65         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 0.45/0.65           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 0.45/0.65              (k3_xboole_0 @ X18 @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.65            = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X37 : $i, X38 : $i]: (r1_tarski @ X37 @ (k2_xboole_0 @ X37 @ X38))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.65  thf(t43_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.45/0.65       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.65         ((r1_tarski @ (k4_xboole_0 @ X27 @ X28) @ X29)
% 0.45/0.65          | ~ (r1_tarski @ X27 @ (k2_xboole_0 @ X28 @ X29)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf(idempotence_k2_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.65  thf('23', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.45/0.65  thf(t46_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X30 : $i, X31 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.45/0.65  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['23', '24'])).
% 0.45/0.65  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.65      inference('demod', [status(thm)], ['22', '25'])).
% 0.45/0.65  thf(t12_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.65  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.65            = (k3_xboole_0 @ sk_A @ X0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '28'])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 0.45/0.65      inference('split', [status(esa)], ['3'])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) & 
% 0.45/0.65             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['29', '32'])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X0 : $i, X2 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C_2)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) & 
% 0.45/0.65             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ sk_C_2))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) & 
% 0.45/0.65             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      ((~ (r1_xboole_0 @ sk_A @ sk_C_2)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) | 
% 0.45/0.65       ~ ((r1_xboole_0 @ sk_A @ sk_B)) | ((r1_xboole_0 @ sk_A @ sk_C_2))),
% 0.45/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.65  thf('39', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['2', '14', '38'])).
% 0.45/0.65  thf('40', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.65         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 0.45/0.65           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 0.45/0.65              (k3_xboole_0 @ X18 @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))
% 0.45/0.65            = (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['41', '42'])).
% 0.45/0.65  thf(t3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.65            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf(t4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.45/0.65          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_A @ sk_B)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('split', [status(esa)], ['3'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      ((![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      ((![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['44', '49'])).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      ((![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.65  thf(t22_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 0.45/0.65      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      ((![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))
% 0.45/0.65            = (k3_xboole_0 @ sk_A @ X0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['43', '56'])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.45/0.65        | (r1_xboole_0 @ sk_A @ sk_C_2))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ sk_C_2)) <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 0.45/0.65      inference('split', [status(esa)], ['58'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.65         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 0.45/0.65           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 0.45/0.65              (k3_xboole_0 @ X18 @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_2 @ X0))
% 0.45/0.65            = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['61', '62'])).
% 0.45/0.65  thf('64', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_2 @ X0))
% 0.45/0.65            = (k3_xboole_0 @ sk_A @ X0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 0.45/0.65      inference('demod', [status(thm)], ['63', '64'])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ sk_C_2) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['57', '65'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      ((((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 0.45/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.45/0.65       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.45/0.65      inference('split', [status(esa)], ['3'])).
% 0.45/0.65  thf('70', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['2', '14', '38', '69'])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      (((r1_xboole_0 @ sk_A @ sk_C_2)) | 
% 0.45/0.65       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.45/0.65      inference('split', [status(esa)], ['58'])).
% 0.45/0.65  thf('72', plain, (((r1_xboole_0 @ sk_A @ sk_C_2))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['2', '14', '38', '71'])).
% 0.45/0.65  thf('73', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['68', '70', '72'])).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.65            = (k3_xboole_0 @ sk_A @ X0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '28'])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X10 @ X11)
% 0.45/0.65          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ (k3_xboole_0 @ X10 @ X11)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X10 @ X11)
% 0.45/0.65          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ (k3_xboole_0 @ X10 @ X11)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('77', plain,
% 0.45/0.65      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X8 @ X6)
% 0.45/0.65          | ~ (r2_hidden @ X8 @ X9)
% 0.45/0.65          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X1 @ X0)
% 0.45/0.65          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.65          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.45/0.65      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X1 @ X0)
% 0.45/0.65          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65          | (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['75', '78'])).
% 0.45/0.65  thf('80', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65          | (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['79'])).
% 0.45/0.65  thf('81', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)) @ 
% 0.45/0.65              (k3_xboole_0 @ sk_A @ X0))
% 0.45/0.65           | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '80'])).
% 0.45/0.65  thf('82', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.65            = (k3_xboole_0 @ sk_A @ X0)))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '28'])).
% 0.45/0.65  thf('83', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.45/0.65              (k3_xboole_0 @ sk_A @ X0))
% 0.45/0.65           | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.45/0.65         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.65  thf('84', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['2', '14', '38', '69'])).
% 0.45/0.65  thf('85', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.45/0.65             (k3_xboole_0 @ sk_A @ X0))
% 0.45/0.65          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C_2))
% 0.45/0.65        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['73', '85'])).
% 0.45/0.65  thf('87', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['68', '70', '72'])).
% 0.45/0.65  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 0.45/0.65      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.45/0.65  thf('90', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['88', '89'])).
% 0.45/0.65  thf('91', plain,
% 0.45/0.65      (![X0 : $i, X2 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('92', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['90', '91'])).
% 0.45/0.65  thf('93', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.65      inference('simplify', [status(thm)], ['92'])).
% 0.45/0.65  thf('94', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.45/0.65      inference('demod', [status(thm)], ['86', '87', '93'])).
% 0.45/0.65  thf('95', plain, ($false), inference('demod', [status(thm)], ['40', '94'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
