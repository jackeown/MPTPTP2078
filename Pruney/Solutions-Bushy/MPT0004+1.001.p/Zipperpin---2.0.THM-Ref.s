%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.utIMv9OpS7

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 109 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  288 ( 957 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t4_xboole_0,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( ? [C: $i] :
                ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
            & ( r1_xboole_0 @ A @ B ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ B )
            & ! [C: $i] :
                ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_xboole_0])).

thf('0',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ( ( k3_xboole_0 @ X3 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ! [X7: $i] :
          ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ~ ! [X7: $i] :
          ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('20',plain,(
    r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['14','17','18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ! [X7: $i] :
        ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('25',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['14','17','18','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('30',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('31',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['21','28','33'])).


%------------------------------------------------------------------------------
