%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0291+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IjCjvKbS2m

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:39 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  363 ( 515 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t98_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ! [C: $i] :
            ( ( r2_hidden @ C @ A )
           => ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t98_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X15 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ X1 )
      | ( X3
       != ( k3_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('6',plain,(
    ! [X1: $i,X4: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ ( k3_tarski @ X0 ) @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X19: $i] :
      ( ( r1_xboole_0 @ X19 @ sk_B )
      | ~ ( r2_hidden @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( sk_D_1 @ ( sk_C_1 @ ( k3_tarski @ sk_A ) @ X0 ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('11',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ ( sk_D_1 @ X4 @ X1 ) )
      | ( X3
       != ( k3_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('12',plain,(
    ! [X1: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( sk_D_1 @ X4 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_tarski @ X0 ) @ X1 ) @ ( sk_D_1 @ ( sk_C_1 @ ( k3_tarski @ X0 ) @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X15 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_tarski @ X0 ) @ X1 ) @ ( k3_xboole_0 @ ( sk_D_1 @ ( sk_C_1 @ ( k3_tarski @ X0 ) @ X1 ) @ X0 ) @ X1 ) )
      | ( r1_xboole_0 @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k3_tarski @ X0 ) @ X1 ) @ ( k3_xboole_0 @ ( sk_D_1 @ ( sk_C_1 @ ( k3_tarski @ X0 ) @ X1 ) @ X0 ) @ X1 ) )
      | ( r1_xboole_0 @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X15 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_tarski @ X1 ) )
      | ~ ( r1_xboole_0 @ ( sk_D_1 @ ( sk_C_1 @ ( k3_tarski @ X1 ) @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_tarski @ sk_A ) )
    | ( r1_xboole_0 @ sk_B @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_B @ ( k3_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('28',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).


%------------------------------------------------------------------------------
