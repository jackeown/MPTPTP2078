%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0274+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3fzgBsGuAQ

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  76 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  440 ( 874 expanded)
%              Number of equality atoms :   31 (  63 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k4_xboole_0 @ X8 @ X10 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,
    ( ( ( ( k2_tarski @ sk_A @ sk_B )
       != ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( r1_xboole_0 @ ( k2_tarski @ X5 @ X7 ) @ X6 )
      | ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,
    ( ( ( ( k2_tarski @ sk_A @ sk_B )
       != ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_C )
      | ( r2_hidden @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( r2_hidden @ sk_B @ sk_C )
      | ( r2_hidden @ sk_A @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( ~ ( r2_hidden @ sk_B @ sk_C )
      & ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
       != ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','13','18','19','20','30'])).


%------------------------------------------------------------------------------
