%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0111+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pnUgDAiQCJ

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 232 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   22
%              Number of atoms          :  346 (1849 expanded)
%              Number of equality atoms :   21 ( 144 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t104_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( ~ ( r2_xboole_0 @ A @ B )
          & ( A != B )
          & ~ ( r2_xboole_0 @ B @ A ) )
    <=> ( r3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( ~ ( r2_xboole_0 @ A @ B )
            & ( A != B )
            & ~ ( r2_xboole_0 @ B @ A ) )
      <=> ( r3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t104_xboole_1])).

thf('0',plain,
    ( ~ ( r3_xboole_0 @ sk_A @ sk_B )
    | ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r3_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_B @ sk_A )
    | ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r3_xboole_0 @ sk_A @ sk_B )
    | ( sk_A != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_A != sk_B )
    | ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('7',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_B @ sk_A )
    | ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( r3_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ~ ( r3_xboole_0 @ sk_A @ sk_A )
   <= ( ~ ( r3_xboole_0 @ sk_A @ sk_B )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(reflexivity_r3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( r3_xboole_0 @ A @ A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( r3_xboole_0 @ X6 @ X6 ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_xboole_0])).

thf('12',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
    | ( sk_A != sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['6','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['5','13'])).

thf('15',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_B @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['3','14'])).

thf('16',plain,
    ( ~ ( r3_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( ( r2_xboole_0 @ sk_A @ sk_B )
      | ( r2_xboole_0 @ sk_B @ sk_A ) )
   <= ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('19',plain,
    ( ( ( r2_xboole_0 @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('21',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ( r1_tarski @ sk_A @ sk_B ) )
   <= ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r3_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('23',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ( r3_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r3_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('25',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    r3_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['2','25'])).

thf('27',plain,
    ( ~ ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,
    ( ( r3_xboole_0 @ sk_A @ sk_B )
   <= ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X4 @ X3 )
      | ~ ( r3_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('32',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r3_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['26'])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['5','13'])).

thf('38',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r3_xboole_0 @ sk_A @ sk_B )
    | ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( r2_xboole_0 @ sk_B @ sk_A )
   <= ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ~ ( r2_xboole_0 @ sk_B @ sk_A )
    | ~ ( r3_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('42',plain,(
    ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['26','41'])).

thf('43',plain,(
    ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('46',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['5','13'])).

thf('48',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['29','48'])).


%------------------------------------------------------------------------------
