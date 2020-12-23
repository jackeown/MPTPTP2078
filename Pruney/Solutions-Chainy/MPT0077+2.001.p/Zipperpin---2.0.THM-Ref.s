%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gssgRcdxrP

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:49 EST 2020

% Result     : Theorem 4.30s
% Output     : Refutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 480 expanded)
%              Number of leaves         :   28 ( 148 expanded)
%              Depth                    :   18
%              Number of atoms          : 1115 (4533 expanded)
%              Number of equality atoms :   71 ( 186 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_xboole_0 @ X31 @ X32 )
      | ( r1_xboole_0 @ X30 @ X32 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_xboole_0 @ X31 @ X32 )
      | ( r1_xboole_0 @ X30 @ X32 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
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

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('31',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('40',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ ( k4_xboole_0 @ X28 @ X29 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['38','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('53',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('56',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['56','57'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('59',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('65',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('74',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('75',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('76',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('79',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('80',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','83'])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','86'])).

thf('88',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('90',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('92',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','86'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('100',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('101',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','103'])).

thf('105',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','95'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('110',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('111',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','52'])).

thf('112',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('114',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_xboole_0 @ X31 @ X32 )
      | ( r1_xboole_0 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('118',plain,(
    r1_xboole_0 @ sk_B_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('120',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['108','109','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ X0 ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','122'])).

thf('124',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['46','123'])).

thf('125',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('126',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['27','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gssgRcdxrP
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.30/4.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.30/4.53  % Solved by: fo/fo7.sh
% 4.30/4.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.30/4.53  % done 6785 iterations in 4.074s
% 4.30/4.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.30/4.53  % SZS output start Refutation
% 4.30/4.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.30/4.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.30/4.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.30/4.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.30/4.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.30/4.53  thf(sk_A_type, type, sk_A: $i).
% 4.30/4.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.30/4.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.30/4.53  thf(sk_B_type, type, sk_B: $i > $i).
% 4.30/4.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.30/4.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.30/4.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.30/4.53  thf(t70_xboole_1, conjecture,
% 4.30/4.53    (![A:$i,B:$i,C:$i]:
% 4.30/4.53     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.30/4.53            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.30/4.53       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.30/4.53            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 4.30/4.53  thf(zf_stmt_0, negated_conjecture,
% 4.30/4.53    (~( ![A:$i,B:$i,C:$i]:
% 4.30/4.53        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.30/4.53               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.30/4.53          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.30/4.53               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 4.30/4.53    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 4.30/4.53  thf('0', plain,
% 4.30/4.53      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 4.30/4.53        | ~ (r1_xboole_0 @ sk_A @ sk_B_1)
% 4.30/4.53        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 4.30/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.53  thf('1', plain,
% 4.30/4.53      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 4.30/4.53         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 4.30/4.53      inference('split', [status(esa)], ['0'])).
% 4.30/4.53  thf('2', plain,
% 4.30/4.53      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))) | 
% 4.30/4.53       ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B_1))),
% 4.30/4.53      inference('split', [status(esa)], ['0'])).
% 4.30/4.53  thf('3', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 4.30/4.53        | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 4.30/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.53  thf('4', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 4.30/4.53      inference('split', [status(esa)], ['3'])).
% 4.30/4.53  thf(symmetry_r1_xboole_0, axiom,
% 4.30/4.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.30/4.53  thf('5', plain,
% 4.30/4.53      (![X10 : $i, X11 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 4.30/4.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.30/4.53  thf('6', plain,
% 4.30/4.53      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 4.30/4.53      inference('sup-', [status(thm)], ['4', '5'])).
% 4.30/4.53  thf(t7_xboole_1, axiom,
% 4.30/4.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.30/4.53  thf('7', plain,
% 4.30/4.53      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 4.30/4.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.30/4.53  thf(t63_xboole_1, axiom,
% 4.30/4.53    (![A:$i,B:$i,C:$i]:
% 4.30/4.53     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 4.30/4.53       ( r1_xboole_0 @ A @ C ) ))).
% 4.30/4.53  thf('8', plain,
% 4.30/4.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.30/4.53         (~ (r1_tarski @ X30 @ X31)
% 4.30/4.53          | ~ (r1_xboole_0 @ X31 @ X32)
% 4.30/4.53          | (r1_xboole_0 @ X30 @ X32))),
% 4.30/4.53      inference('cnf', [status(esa)], [t63_xboole_1])).
% 4.30/4.53  thf('9', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X1 @ X2)
% 4.30/4.53          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 4.30/4.53      inference('sup-', [status(thm)], ['7', '8'])).
% 4.30/4.53  thf('10', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_B_1 @ sk_A))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 4.30/4.53      inference('sup-', [status(thm)], ['6', '9'])).
% 4.30/4.53  thf('11', plain,
% 4.30/4.53      (![X10 : $i, X11 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 4.30/4.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.30/4.53  thf('12', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_B_1))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 4.30/4.53      inference('sup-', [status(thm)], ['10', '11'])).
% 4.30/4.53  thf('13', plain,
% 4.30/4.53      ((~ (r1_xboole_0 @ sk_A @ sk_B_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 4.30/4.53      inference('split', [status(esa)], ['0'])).
% 4.30/4.53  thf('14', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 4.30/4.53       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['12', '13'])).
% 4.30/4.53  thf('15', plain,
% 4.30/4.53      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 4.30/4.53      inference('sup-', [status(thm)], ['4', '5'])).
% 4.30/4.53  thf(commutativity_k2_xboole_0, axiom,
% 4.30/4.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.30/4.53  thf('16', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.30/4.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.30/4.53  thf('17', plain,
% 4.30/4.53      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 4.30/4.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.30/4.53  thf('18', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.30/4.53      inference('sup+', [status(thm)], ['16', '17'])).
% 4.30/4.53  thf('19', plain,
% 4.30/4.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.30/4.53         (~ (r1_tarski @ X30 @ X31)
% 4.30/4.53          | ~ (r1_xboole_0 @ X31 @ X32)
% 4.30/4.53          | (r1_xboole_0 @ X30 @ X32))),
% 4.30/4.53      inference('cnf', [status(esa)], [t63_xboole_1])).
% 4.30/4.53  thf('20', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X0 @ X2)
% 4.30/4.53          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 4.30/4.53      inference('sup-', [status(thm)], ['18', '19'])).
% 4.30/4.53  thf('21', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_C_1 @ sk_A))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 4.30/4.53      inference('sup-', [status(thm)], ['15', '20'])).
% 4.30/4.53  thf('22', plain,
% 4.30/4.53      (![X10 : $i, X11 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 4.30/4.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.30/4.53  thf('23', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 4.30/4.53      inference('sup-', [status(thm)], ['21', '22'])).
% 4.30/4.53  thf('24', plain,
% 4.30/4.53      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 4.30/4.53      inference('split', [status(esa)], ['0'])).
% 4.30/4.53  thf('25', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 4.30/4.53       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['23', '24'])).
% 4.30/4.53  thf('26', plain,
% 4.30/4.53      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 4.30/4.53      inference('sat_resolution*', [status(thm)], ['2', '14', '25'])).
% 4.30/4.53  thf('27', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 4.30/4.53      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 4.30/4.53  thf('28', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 4.30/4.53        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 4.30/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.53  thf('29', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 4.30/4.53      inference('split', [status(esa)], ['28'])).
% 4.30/4.53  thf('30', plain,
% 4.30/4.53      (![X10 : $i, X11 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 4.30/4.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.30/4.53  thf('31', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_C_1 @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['29', '30'])).
% 4.30/4.53  thf(t7_xboole_0, axiom,
% 4.30/4.53    (![A:$i]:
% 4.30/4.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.30/4.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 4.30/4.53  thf('32', plain,
% 4.30/4.53      (![X16 : $i]:
% 4.30/4.53         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 4.30/4.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.30/4.53  thf(t4_xboole_0, axiom,
% 4.30/4.53    (![A:$i,B:$i]:
% 4.30/4.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.30/4.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.30/4.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.30/4.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.30/4.53  thf('33', plain,
% 4.30/4.53      (![X12 : $i, X14 : $i, X15 : $i]:
% 4.30/4.53         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 4.30/4.53          | ~ (r1_xboole_0 @ X12 @ X15))),
% 4.30/4.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.30/4.53  thf('34', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['32', '33'])).
% 4.30/4.53  thf('35', plain,
% 4.30/4.53      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['31', '34'])).
% 4.30/4.53  thf('36', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 4.30/4.53       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 4.30/4.53      inference('split', [status(esa)], ['28'])).
% 4.30/4.53  thf('37', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 4.30/4.53      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '36'])).
% 4.30/4.53  thf('38', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 4.30/4.53      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 4.30/4.53  thf(commutativity_k3_xboole_0, axiom,
% 4.30/4.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.30/4.53  thf('39', plain,
% 4.30/4.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.30/4.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.30/4.53  thf(t51_xboole_1, axiom,
% 4.30/4.53    (![A:$i,B:$i]:
% 4.30/4.53     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 4.30/4.53       ( A ) ))).
% 4.30/4.53  thf('40', plain,
% 4.30/4.53      (![X28 : $i, X29 : $i]:
% 4.30/4.53         ((k2_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ (k4_xboole_0 @ X28 @ X29))
% 4.30/4.53           = (X28))),
% 4.30/4.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 4.30/4.53  thf('41', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 4.30/4.53           = (X0))),
% 4.30/4.53      inference('sup+', [status(thm)], ['39', '40'])).
% 4.30/4.53  thf('42', plain,
% 4.30/4.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_A))),
% 4.30/4.53      inference('sup+', [status(thm)], ['38', '41'])).
% 4.30/4.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.30/4.53  thf('43', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 4.30/4.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.30/4.53  thf(t12_xboole_1, axiom,
% 4.30/4.53    (![A:$i,B:$i]:
% 4.30/4.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.30/4.53  thf('44', plain,
% 4.30/4.53      (![X17 : $i, X18 : $i]:
% 4.30/4.53         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 4.30/4.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.30/4.53  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['43', '44'])).
% 4.30/4.53  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 4.30/4.53      inference('demod', [status(thm)], ['42', '45'])).
% 4.30/4.53  thf('47', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 4.30/4.53      inference('split', [status(esa)], ['3'])).
% 4.30/4.53  thf('48', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['32', '33'])).
% 4.30/4.53  thf('49', plain,
% 4.30/4.53      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['47', '48'])).
% 4.30/4.53  thf('50', plain,
% 4.30/4.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.30/4.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.30/4.53  thf('51', plain,
% 4.30/4.53      ((((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 4.30/4.53         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 4.30/4.53      inference('demod', [status(thm)], ['49', '50'])).
% 4.30/4.53  thf('52', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 4.30/4.53       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 4.30/4.53      inference('split', [status(esa)], ['3'])).
% 4.30/4.53  thf('53', plain, (((r1_xboole_0 @ sk_A @ sk_B_1))),
% 4.30/4.53      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '52'])).
% 4.30/4.53  thf('54', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 4.30/4.53      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 4.30/4.53  thf('55', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 4.30/4.53           = (X0))),
% 4.30/4.53      inference('sup+', [status(thm)], ['39', '40'])).
% 4.30/4.53  thf('56', plain,
% 4.30/4.53      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 4.30/4.53      inference('sup+', [status(thm)], ['54', '55'])).
% 4.30/4.53  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['43', '44'])).
% 4.30/4.53  thf('58', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 4.30/4.53      inference('demod', [status(thm)], ['56', '57'])).
% 4.30/4.53  thf(t41_xboole_1, axiom,
% 4.30/4.53    (![A:$i,B:$i,C:$i]:
% 4.30/4.53     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 4.30/4.53       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.30/4.53  thf('59', plain,
% 4.30/4.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 4.30/4.53           = (k4_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 4.30/4.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.30/4.53  thf('60', plain,
% 4.30/4.53      (![X0 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ sk_A @ X0)
% 4.30/4.53           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 4.30/4.53      inference('sup+', [status(thm)], ['58', '59'])).
% 4.30/4.53  thf('61', plain,
% 4.30/4.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 4.30/4.53           = (k4_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 4.30/4.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.30/4.53  thf(t39_xboole_1, axiom,
% 4.30/4.53    (![A:$i,B:$i]:
% 4.30/4.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.30/4.53  thf('62', plain,
% 4.30/4.53      (![X20 : $i, X21 : $i]:
% 4.30/4.53         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 4.30/4.53           = (k2_xboole_0 @ X20 @ X21))),
% 4.30/4.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.30/4.53  thf('63', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.53         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 4.30/4.53           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 4.30/4.53      inference('sup+', [status(thm)], ['61', '62'])).
% 4.30/4.53  thf(t48_xboole_1, axiom,
% 4.30/4.53    (![A:$i,B:$i]:
% 4.30/4.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.30/4.53  thf('64', plain,
% 4.30/4.53      (![X26 : $i, X27 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 4.30/4.53           = (k3_xboole_0 @ X26 @ X27))),
% 4.30/4.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.30/4.53  thf('65', plain,
% 4.30/4.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 4.30/4.53           = (k4_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 4.30/4.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.30/4.53  thf('66', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.53         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 4.30/4.53           = (k4_xboole_0 @ X2 @ 
% 4.30/4.53              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 4.30/4.53      inference('sup+', [status(thm)], ['64', '65'])).
% 4.30/4.53  thf('67', plain,
% 4.30/4.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 4.30/4.53           = (k4_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 4.30/4.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.30/4.53  thf('68', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.53         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 4.30/4.53           = (k4_xboole_0 @ X2 @ 
% 4.30/4.53              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 4.30/4.53      inference('demod', [status(thm)], ['66', '67'])).
% 4.30/4.53  thf('69', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.30/4.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 4.30/4.53      inference('sup+', [status(thm)], ['63', '68'])).
% 4.30/4.53  thf('70', plain,
% 4.30/4.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.30/4.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.30/4.53  thf('71', plain,
% 4.30/4.53      (![X20 : $i, X21 : $i]:
% 4.30/4.53         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 4.30/4.53           = (k2_xboole_0 @ X20 @ X21))),
% 4.30/4.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.30/4.53  thf('72', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.30/4.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 4.30/4.53      inference('demod', [status(thm)], ['69', '70', '71'])).
% 4.30/4.53  thf('73', plain,
% 4.30/4.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 4.30/4.53           = (k4_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 4.30/4.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.30/4.53  thf('74', plain,
% 4.30/4.53      (![X16 : $i]:
% 4.30/4.53         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 4.30/4.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.30/4.53  thf(d5_xboole_0, axiom,
% 4.30/4.53    (![A:$i,B:$i,C:$i]:
% 4.30/4.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.30/4.53       ( ![D:$i]:
% 4.30/4.53         ( ( r2_hidden @ D @ C ) <=>
% 4.30/4.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.30/4.53  thf('75', plain,
% 4.30/4.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 4.30/4.53         (~ (r2_hidden @ X8 @ X7)
% 4.30/4.53          | (r2_hidden @ X8 @ X5)
% 4.30/4.53          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 4.30/4.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.30/4.53  thf('76', plain,
% 4.30/4.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 4.30/4.53         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 4.30/4.53      inference('simplify', [status(thm)], ['75'])).
% 4.30/4.53  thf('77', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 4.30/4.53          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 4.30/4.53      inference('sup-', [status(thm)], ['74', '76'])).
% 4.30/4.53  thf('78', plain,
% 4.30/4.53      (![X16 : $i]:
% 4.30/4.53         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 4.30/4.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.30/4.53  thf('79', plain,
% 4.30/4.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 4.30/4.53         (~ (r2_hidden @ X8 @ X7)
% 4.30/4.53          | ~ (r2_hidden @ X8 @ X6)
% 4.30/4.53          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 4.30/4.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.30/4.53  thf('80', plain,
% 4.30/4.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 4.30/4.53         (~ (r2_hidden @ X8 @ X6)
% 4.30/4.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 4.30/4.53      inference('simplify', [status(thm)], ['79'])).
% 4.30/4.53  thf('81', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 4.30/4.53          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['78', '80'])).
% 4.30/4.53  thf('82', plain,
% 4.30/4.53      (![X0 : $i]:
% 4.30/4.53         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 4.30/4.53          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['77', '81'])).
% 4.30/4.53  thf('83', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.30/4.53      inference('simplify', [status(thm)], ['82'])).
% 4.30/4.53  thf('84', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 4.30/4.53           = (k1_xboole_0))),
% 4.30/4.53      inference('sup+', [status(thm)], ['73', '83'])).
% 4.30/4.53  thf('85', plain,
% 4.30/4.53      (![X20 : $i, X21 : $i]:
% 4.30/4.53         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 4.30/4.53           = (k2_xboole_0 @ X20 @ X21))),
% 4.30/4.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.30/4.53  thf('86', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 4.30/4.53      inference('demod', [status(thm)], ['84', '85'])).
% 4.30/4.53  thf('87', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.30/4.53      inference('demod', [status(thm)], ['72', '86'])).
% 4.30/4.53  thf('88', plain,
% 4.30/4.53      (![X12 : $i, X13 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X12 @ X13)
% 4.30/4.53          | (r2_hidden @ (sk_C @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 4.30/4.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.30/4.53  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.30/4.53      inference('simplify', [status(thm)], ['82'])).
% 4.30/4.53  thf('90', plain,
% 4.30/4.53      (![X26 : $i, X27 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 4.30/4.53           = (k3_xboole_0 @ X26 @ X27))),
% 4.30/4.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.30/4.53  thf('91', plain,
% 4.30/4.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 4.30/4.53      inference('sup+', [status(thm)], ['89', '90'])).
% 4.30/4.53  thf(t3_boole, axiom,
% 4.30/4.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.30/4.53  thf('92', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 4.30/4.53      inference('cnf', [status(esa)], [t3_boole])).
% 4.30/4.53  thf('93', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.30/4.53      inference('demod', [status(thm)], ['91', '92'])).
% 4.30/4.53  thf('94', plain,
% 4.30/4.53      (![X12 : $i, X14 : $i, X15 : $i]:
% 4.30/4.53         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 4.30/4.53          | ~ (r1_xboole_0 @ X12 @ X15))),
% 4.30/4.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.30/4.53  thf('95', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['93', '94'])).
% 4.30/4.53  thf('96', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X1 @ X0)
% 4.30/4.53          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['88', '95'])).
% 4.30/4.53  thf('97', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.30/4.53             k1_xboole_0)
% 4.30/4.53          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['87', '96'])).
% 4.30/4.53  thf('98', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.30/4.53      inference('demod', [status(thm)], ['72', '86'])).
% 4.30/4.53  thf('99', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 4.30/4.53          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 4.30/4.53      inference('sup-', [status(thm)], ['74', '76'])).
% 4.30/4.53  thf('100', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 4.30/4.53      inference('cnf', [status(esa)], [t3_boole])).
% 4.30/4.53  thf('101', plain,
% 4.30/4.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 4.30/4.53         (~ (r2_hidden @ X8 @ X6)
% 4.30/4.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 4.30/4.53      inference('simplify', [status(thm)], ['79'])).
% 4.30/4.53  thf('102', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['100', '101'])).
% 4.30/4.53  thf('103', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.30/4.53      inference('condensation', [status(thm)], ['102'])).
% 4.30/4.53  thf('104', plain,
% 4.30/4.53      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['99', '103'])).
% 4.30/4.53  thf('105', plain,
% 4.30/4.53      (![X26 : $i, X27 : $i]:
% 4.30/4.53         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 4.30/4.53           = (k3_xboole_0 @ X26 @ X27))),
% 4.30/4.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.30/4.53  thf('106', plain,
% 4.30/4.53      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 4.30/4.53      inference('sup+', [status(thm)], ['104', '105'])).
% 4.30/4.53  thf('107', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X1 @ X0)
% 4.30/4.53          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 4.30/4.53      inference('sup-', [status(thm)], ['88', '95'])).
% 4.30/4.53  thf('108', plain,
% 4.30/4.53      (![X0 : $i]:
% 4.30/4.53         (~ (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 4.30/4.53          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 4.30/4.53      inference('sup-', [status(thm)], ['106', '107'])).
% 4.30/4.53  thf('109', plain,
% 4.30/4.53      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 4.30/4.53      inference('sup+', [status(thm)], ['104', '105'])).
% 4.30/4.53  thf('110', plain,
% 4.30/4.53      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 4.30/4.53      inference('split', [status(esa)], ['3'])).
% 4.30/4.53  thf('111', plain, (((r1_xboole_0 @ sk_A @ sk_B_1))),
% 4.30/4.53      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '52'])).
% 4.30/4.53  thf('112', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 4.30/4.53      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 4.30/4.53  thf('113', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 4.30/4.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.30/4.53  thf('114', plain,
% 4.30/4.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.30/4.53         (~ (r1_tarski @ X30 @ X31)
% 4.30/4.53          | ~ (r1_xboole_0 @ X31 @ X32)
% 4.30/4.53          | (r1_xboole_0 @ X30 @ X32))),
% 4.30/4.53      inference('cnf', [status(esa)], [t63_xboole_1])).
% 4.30/4.53  thf('115', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ k1_xboole_0 @ X1) | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.30/4.53      inference('sup-', [status(thm)], ['113', '114'])).
% 4.30/4.53  thf('116', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_B_1)),
% 4.30/4.53      inference('sup-', [status(thm)], ['112', '115'])).
% 4.30/4.53  thf('117', plain,
% 4.30/4.53      (![X10 : $i, X11 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 4.30/4.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.30/4.53  thf('118', plain, ((r1_xboole_0 @ sk_B_1 @ k1_xboole_0)),
% 4.30/4.53      inference('sup-', [status(thm)], ['116', '117'])).
% 4.30/4.53  thf('119', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ k1_xboole_0 @ X1) | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.30/4.53      inference('sup-', [status(thm)], ['113', '114'])).
% 4.30/4.53  thf('120', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 4.30/4.53      inference('sup-', [status(thm)], ['118', '119'])).
% 4.30/4.53  thf('121', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.30/4.53      inference('demod', [status(thm)], ['108', '109', '120'])).
% 4.30/4.53  thf('122', plain,
% 4.30/4.53      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.30/4.53      inference('demod', [status(thm)], ['97', '98', '121'])).
% 4.30/4.53  thf('123', plain,
% 4.30/4.53      (![X0 : $i]:
% 4.30/4.53         (r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ X0) @ (k4_xboole_0 @ sk_A @ X0))),
% 4.30/4.53      inference('sup+', [status(thm)], ['60', '122'])).
% 4.30/4.53  thf('124', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 4.30/4.53      inference('sup+', [status(thm)], ['46', '123'])).
% 4.30/4.53  thf('125', plain,
% 4.30/4.53      (![X10 : $i, X11 : $i]:
% 4.30/4.53         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 4.30/4.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.30/4.53  thf('126', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 4.30/4.53      inference('sup-', [status(thm)], ['124', '125'])).
% 4.30/4.53  thf('127', plain, ($false), inference('demod', [status(thm)], ['27', '126'])).
% 4.30/4.53  
% 4.30/4.53  % SZS output end Refutation
% 4.30/4.53  
% 4.30/4.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
