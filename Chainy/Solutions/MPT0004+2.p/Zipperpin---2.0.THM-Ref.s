%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0004+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2vGToYYWL8

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  315 ( 642 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t4_xboole_0,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( ? [C: $i] :
                ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) )
            & ( r1_xboole_0 @ ( A @ B ) ) )
        & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
            & ! [C: $i] :
                ~ ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_xboole_0])).

thf('0',plain,(
    ! [X52: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
      | ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
    | ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X52: $i] :
      ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ ( X31 @ X32 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ ( X31 @ X32 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X31 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
      = o_0_0_xboole_0 )
   <= ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
   <= ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( X8 @ X9 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) )
   <= ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
      & ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('14',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
   <= ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('16',plain,
    ( ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
   <= ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
    | ~ ! [X52: $i] :
          ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
    | ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_C_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ( r2_hidden @ ( sk_B @ X10 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,
    ( ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) )
   <= ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) )
   <= ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X36: $i] :
      ( ( X36 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
      = o_0_0_xboole_0 )
   <= ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( X31 @ X33 ) )
      | ( ( k3_xboole_0 @ ( X31 @ X33 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( X31 @ X33 ) )
      | ( ( k3_xboole_0 @ ( X31 @ X33 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) )
   <= ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
   <= ! [X52: $i] :
        ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
   <= ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) )
    | ~ ! [X52: $i] :
          ~ ( r2_hidden @ ( X52 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','14','17','18','19','33'])).

%------------------------------------------------------------------------------
