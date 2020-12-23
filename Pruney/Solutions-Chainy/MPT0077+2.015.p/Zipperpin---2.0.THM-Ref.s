%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.08w5EOYQpG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:51 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 236 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :   19
%              Number of atoms          :  643 (2273 expanded)
%              Number of equality atoms :   38 (  51 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_xboole_0 @ X24 @ X25 )
      | ( r1_xboole_0 @ X23 @ X25 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_xboole_0 @ X24 @ X25 )
      | ( r1_xboole_0 @ X23 @ X25 ) ) ),
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

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('31',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('35',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('45',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','25','48'])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['42','58'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('60',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('63',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('70',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['27','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.08w5EOYQpG
% 0.12/0.36  % Computer   : n005.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 15:02:18 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 2.00/2.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.00/2.23  % Solved by: fo/fo7.sh
% 2.00/2.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.00/2.23  % done 1776 iterations in 1.758s
% 2.00/2.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.00/2.23  % SZS output start Refutation
% 2.00/2.23  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.00/2.23  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.00/2.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.00/2.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.00/2.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.00/2.23  thf(sk_B_type, type, sk_B: $i).
% 2.00/2.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.00/2.23  thf(sk_A_type, type, sk_A: $i).
% 2.00/2.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.00/2.23  thf(t70_xboole_1, conjecture,
% 2.00/2.23    (![A:$i,B:$i,C:$i]:
% 2.00/2.23     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.00/2.23            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.00/2.23       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.00/2.23            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.00/2.23  thf(zf_stmt_0, negated_conjecture,
% 2.00/2.23    (~( ![A:$i,B:$i,C:$i]:
% 2.00/2.23        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.00/2.23               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.00/2.23          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.00/2.23               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 2.00/2.23    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 2.00/2.23  thf('0', plain,
% 2.00/2.23      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 2.00/2.23        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 2.00/2.23        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 2.00/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.23  thf('1', plain,
% 2.00/2.23      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 2.00/2.23         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 2.00/2.23      inference('split', [status(esa)], ['0'])).
% 2.00/2.23  thf('2', plain,
% 2.00/2.23      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 2.00/2.23       ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 2.00/2.23      inference('split', [status(esa)], ['0'])).
% 2.00/2.23  thf('3', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 2.00/2.23        | (r1_xboole_0 @ sk_A @ sk_B))),
% 2.00/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.23  thf('4', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 2.00/2.23      inference('split', [status(esa)], ['3'])).
% 2.00/2.23  thf(symmetry_r1_xboole_0, axiom,
% 2.00/2.23    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.00/2.23  thf('5', plain,
% 2.00/2.23      (![X5 : $i, X6 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 2.00/2.23      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.00/2.23  thf('6', plain,
% 2.00/2.23      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 2.00/2.23      inference('sup-', [status(thm)], ['4', '5'])).
% 2.00/2.23  thf(t7_xboole_1, axiom,
% 2.00/2.23    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.00/2.23  thf('7', plain,
% 2.00/2.23      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 2.00/2.23      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.00/2.23  thf(t63_xboole_1, axiom,
% 2.00/2.23    (![A:$i,B:$i,C:$i]:
% 2.00/2.23     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 2.00/2.23       ( r1_xboole_0 @ A @ C ) ))).
% 2.00/2.23  thf('8', plain,
% 2.00/2.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.00/2.23         (~ (r1_tarski @ X23 @ X24)
% 2.00/2.23          | ~ (r1_xboole_0 @ X24 @ X25)
% 2.00/2.23          | (r1_xboole_0 @ X23 @ X25))),
% 2.00/2.23      inference('cnf', [status(esa)], [t63_xboole_1])).
% 2.00/2.23  thf('9', plain,
% 2.00/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X1 @ X2)
% 2.00/2.23          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.00/2.23      inference('sup-', [status(thm)], ['7', '8'])).
% 2.00/2.23  thf('10', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_B @ sk_A))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 2.00/2.23      inference('sup-', [status(thm)], ['6', '9'])).
% 2.00/2.23  thf('11', plain,
% 2.00/2.23      (![X5 : $i, X6 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 2.00/2.23      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.00/2.23  thf('12', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ sk_B))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 2.00/2.23      inference('sup-', [status(thm)], ['10', '11'])).
% 2.00/2.23  thf('13', plain,
% 2.00/2.23      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.00/2.23      inference('split', [status(esa)], ['0'])).
% 2.00/2.23  thf('14', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 2.00/2.23       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 2.00/2.23      inference('sup-', [status(thm)], ['12', '13'])).
% 2.00/2.23  thf('15', plain,
% 2.00/2.23      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 2.00/2.23      inference('sup-', [status(thm)], ['4', '5'])).
% 2.00/2.23  thf(commutativity_k2_xboole_0, axiom,
% 2.00/2.23    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.00/2.23  thf('16', plain,
% 2.00/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.00/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.00/2.23  thf('17', plain,
% 2.00/2.23      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 2.00/2.23      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.00/2.23  thf('18', plain,
% 2.00/2.23      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.00/2.23      inference('sup+', [status(thm)], ['16', '17'])).
% 2.00/2.23  thf('19', plain,
% 2.00/2.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.00/2.23         (~ (r1_tarski @ X23 @ X24)
% 2.00/2.23          | ~ (r1_xboole_0 @ X24 @ X25)
% 2.00/2.23          | (r1_xboole_0 @ X23 @ X25))),
% 2.00/2.23      inference('cnf', [status(esa)], [t63_xboole_1])).
% 2.00/2.23  thf('20', plain,
% 2.00/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X0 @ X2)
% 2.00/2.23          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.00/2.23      inference('sup-', [status(thm)], ['18', '19'])).
% 2.00/2.23  thf('21', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_C_1 @ sk_A))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 2.00/2.23      inference('sup-', [status(thm)], ['15', '20'])).
% 2.00/2.23  thf('22', plain,
% 2.00/2.23      (![X5 : $i, X6 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 2.00/2.23      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.00/2.23  thf('23', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 2.00/2.23      inference('sup-', [status(thm)], ['21', '22'])).
% 2.00/2.23  thf('24', plain,
% 2.00/2.23      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 2.00/2.23      inference('split', [status(esa)], ['0'])).
% 2.00/2.23  thf('25', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 2.00/2.23       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 2.00/2.23      inference('sup-', [status(thm)], ['23', '24'])).
% 2.00/2.23  thf('26', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 2.00/2.23      inference('sat_resolution*', [status(thm)], ['2', '14', '25'])).
% 2.00/2.23  thf('27', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 2.00/2.23      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 2.00/2.23  thf('28', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 2.00/2.23        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 2.00/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.23  thf('29', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 2.00/2.23      inference('split', [status(esa)], ['28'])).
% 2.00/2.23  thf('30', plain,
% 2.00/2.23      (![X5 : $i, X6 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 2.00/2.23      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.00/2.23  thf('31', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_C_1 @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 2.00/2.23      inference('sup-', [status(thm)], ['29', '30'])).
% 2.00/2.23  thf(d7_xboole_0, axiom,
% 2.00/2.23    (![A:$i,B:$i]:
% 2.00/2.23     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.00/2.23       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.00/2.23  thf('32', plain,
% 2.00/2.23      (![X2 : $i, X3 : $i]:
% 2.00/2.23         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.00/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.00/2.23  thf('33', plain,
% 2.00/2.23      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 2.00/2.23      inference('sup-', [status(thm)], ['31', '32'])).
% 2.00/2.23  thf('34', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 2.00/2.23       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 2.00/2.23      inference('split', [status(esa)], ['28'])).
% 2.00/2.23  thf('35', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 2.00/2.23      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '34'])).
% 2.00/2.23  thf('36', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 2.00/2.23      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 2.00/2.23  thf(t51_xboole_1, axiom,
% 2.00/2.23    (![A:$i,B:$i]:
% 2.00/2.23     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.00/2.23       ( A ) ))).
% 2.00/2.23  thf('37', plain,
% 2.00/2.23      (![X21 : $i, X22 : $i]:
% 2.00/2.23         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 2.00/2.23           = (X21))),
% 2.00/2.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.00/2.23  thf('38', plain,
% 2.00/2.23      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 2.00/2.23      inference('sup+', [status(thm)], ['36', '37'])).
% 2.00/2.23  thf('39', plain,
% 2.00/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.00/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.00/2.23  thf(t1_boole, axiom,
% 2.00/2.23    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.00/2.23  thf('40', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 2.00/2.23      inference('cnf', [status(esa)], [t1_boole])).
% 2.00/2.23  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.00/2.23      inference('sup+', [status(thm)], ['39', '40'])).
% 2.00/2.23  thf('42', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 2.00/2.23      inference('demod', [status(thm)], ['38', '41'])).
% 2.00/2.23  thf('43', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.00/2.23      inference('split', [status(esa)], ['3'])).
% 2.00/2.23  thf('44', plain,
% 2.00/2.23      (![X5 : $i, X6 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 2.00/2.23      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.00/2.23  thf('45', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_B @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.00/2.23      inference('sup-', [status(thm)], ['43', '44'])).
% 2.00/2.23  thf('46', plain,
% 2.00/2.23      (![X2 : $i, X3 : $i]:
% 2.00/2.23         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.00/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.00/2.23  thf('47', plain,
% 2.00/2.23      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))
% 2.00/2.23         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 2.00/2.23      inference('sup-', [status(thm)], ['45', '46'])).
% 2.00/2.23  thf('48', plain,
% 2.00/2.23      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 2.00/2.23       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 2.00/2.23      inference('split', [status(esa)], ['3'])).
% 2.00/2.23  thf('49', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 2.00/2.23      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '48'])).
% 2.00/2.23  thf('50', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 2.00/2.23      inference('simpl_trail', [status(thm)], ['47', '49'])).
% 2.00/2.23  thf('51', plain,
% 2.00/2.23      (![X21 : $i, X22 : $i]:
% 2.00/2.23         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 2.00/2.23           = (X21))),
% 2.00/2.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.00/2.23  thf('52', plain,
% 2.00/2.23      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 2.00/2.23      inference('sup+', [status(thm)], ['50', '51'])).
% 2.00/2.23  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.00/2.23      inference('sup+', [status(thm)], ['39', '40'])).
% 2.00/2.23  thf('54', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.00/2.23      inference('demod', [status(thm)], ['52', '53'])).
% 2.00/2.23  thf(t42_xboole_1, axiom,
% 2.00/2.23    (![A:$i,B:$i,C:$i]:
% 2.00/2.23     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.00/2.23       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.00/2.23  thf('55', plain,
% 2.00/2.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.00/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X18) @ X17)
% 2.00/2.23           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 2.00/2.23              (k4_xboole_0 @ X18 @ X17)))),
% 2.00/2.23      inference('cnf', [status(esa)], [t42_xboole_1])).
% 2.00/2.23  thf('56', plain,
% 2.00/2.23      (![X0 : $i]:
% 2.00/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 2.00/2.23           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 2.00/2.23      inference('sup+', [status(thm)], ['54', '55'])).
% 2.00/2.23  thf(t48_xboole_1, axiom,
% 2.00/2.23    (![A:$i,B:$i]:
% 2.00/2.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.00/2.23  thf('57', plain,
% 2.00/2.23      (![X19 : $i, X20 : $i]:
% 2.00/2.23         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 2.00/2.23           = (k3_xboole_0 @ X19 @ X20))),
% 2.00/2.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.00/2.23  thf('58', plain,
% 2.00/2.23      (![X0 : $i]:
% 2.00/2.23         ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ 
% 2.00/2.23           (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))
% 2.00/2.23           = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A))),
% 2.00/2.23      inference('sup+', [status(thm)], ['56', '57'])).
% 2.00/2.23  thf('59', plain,
% 2.00/2.23      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ 
% 2.00/2.23         (k2_xboole_0 @ sk_B @ sk_C_1))
% 2.00/2.23         = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 2.00/2.23      inference('sup+', [status(thm)], ['42', '58'])).
% 2.00/2.23  thf(t3_boole, axiom,
% 2.00/2.23    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.00/2.23  thf('60', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 2.00/2.23      inference('cnf', [status(esa)], [t3_boole])).
% 2.00/2.23  thf('61', plain,
% 2.00/2.23      (![X19 : $i, X20 : $i]:
% 2.00/2.23         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 2.00/2.23           = (k3_xboole_0 @ X19 @ X20))),
% 2.00/2.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.00/2.23  thf('62', plain,
% 2.00/2.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.00/2.23      inference('sup+', [status(thm)], ['60', '61'])).
% 2.00/2.23  thf(t2_boole, axiom,
% 2.00/2.23    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.00/2.23  thf('63', plain,
% 2.00/2.23      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 2.00/2.23      inference('cnf', [status(esa)], [t2_boole])).
% 2.00/2.23  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.00/2.23      inference('demod', [status(thm)], ['62', '63'])).
% 2.00/2.23  thf('65', plain,
% 2.00/2.23      (((k1_xboole_0) = (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 2.00/2.23      inference('demod', [status(thm)], ['59', '64'])).
% 2.00/2.23  thf('66', plain,
% 2.00/2.23      (![X2 : $i, X4 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 2.00/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.00/2.23  thf('67', plain,
% 2.00/2.23      ((((k1_xboole_0) != (k1_xboole_0))
% 2.00/2.23        | (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 2.00/2.23      inference('sup-', [status(thm)], ['65', '66'])).
% 2.00/2.23  thf('68', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 2.00/2.23      inference('simplify', [status(thm)], ['67'])).
% 2.00/2.23  thf('69', plain,
% 2.00/2.23      (![X5 : $i, X6 : $i]:
% 2.00/2.23         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 2.00/2.23      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.00/2.23  thf('70', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 2.00/2.23      inference('sup-', [status(thm)], ['68', '69'])).
% 2.00/2.23  thf('71', plain, ($false), inference('demod', [status(thm)], ['27', '70'])).
% 2.00/2.23  
% 2.00/2.23  % SZS output end Refutation
% 2.00/2.23  
% 2.00/2.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
