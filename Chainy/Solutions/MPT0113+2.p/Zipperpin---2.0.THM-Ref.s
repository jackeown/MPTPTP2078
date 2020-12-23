%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0113+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iw6EqnAg18

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   51 (  62 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  248 ( 351 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
     => ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
       => ( ( r1_tarski @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) )
   <= ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('2',plain,(
    ! [X198: $i,X199: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X198 @ X199 ) @ X198 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    r1_tarski @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('4',plain,(
    ! [X124: $i,X125: $i] :
      ( ( ( k2_xboole_0 @ ( X125 @ X124 ) )
        = X124 )
      | ~ ( r1_tarski @ ( X125 @ X124 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('6',plain,(
    ! [X121: $i,X122: $i,X123: $i] :
      ( ( r1_tarski @ ( X121 @ X122 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X121 @ X123 ) @ X122 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ X0 ) )
      | ( r1_tarski @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference('sat_resolution*',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,(
    r1_tarski @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('15',plain,(
    ! [X322: $i,X323: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X322 @ X323 ) @ X323 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('16',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('19',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('20',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) )
        & ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('22',plain,(
    ! [X316: $i,X317: $i,X318: $i] :
      ( ( r1_xboole_0 @ ( X316 @ X317 ) )
      | ~ ( r1_xboole_0 @ ( X316 @ ( k3_xboole_0 @ ( X317 @ X318 ) ) ) )
      | ~ ( r1_tarski @ ( X316 @ X318 ) ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( X2 @ o_0_0_xboole_0 ) )
      | ~ ( r1_tarski @ ( X2 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r1_xboole_0 @ ( X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X280: $i] :
      ( r1_xboole_0 @ ( X280 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    ! [X280: $i] :
      ( r1_xboole_0 @ ( X280 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( X2 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r1_xboole_0 @ ( X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['13','28'])).

%------------------------------------------------------------------------------
