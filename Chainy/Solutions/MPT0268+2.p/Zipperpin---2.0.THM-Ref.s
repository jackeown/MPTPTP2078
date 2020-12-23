%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0268+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ilMOD75tyw

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 26.67s
% Output     : Refutation 26.67s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  342 ( 624 expanded)
%              Number of equality atoms :   40 (  71 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ ( k1_tarski @ B ) ) )
        = A )
    <=> ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( A @ ( k1_tarski @ B ) ) )
          = A )
      <=> ~ ( r2_hidden @ ( B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) )
    | ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) )
   <= ~ ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) )
    | ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = sk_A_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) )
    | ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) )
   <= ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = sk_A_2 )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = sk_A_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k4_xboole_0 @ ( B @ ( k1_tarski @ C ) ) ) ) )
    <=> ( ( r2_hidden @ ( A @ B ) )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X1179: $i,X1180: $i,X1181: $i] :
      ( ( X1179 != X1181 )
      | ~ ( r2_hidden @ ( X1179 @ ( k4_xboole_0 @ ( X1180 @ ( k1_tarski @ X1181 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X1180: $i,X1181: $i] :
      ~ ( r2_hidden @ ( X1181 @ ( k4_xboole_0 @ ( X1180 @ ( k1_tarski @ X1181 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = sk_A_2 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != sk_A_2 )
    | ~ ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ ( A @ B ) @ C ) )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ ( A @ C ) )
        & ( ( r2_hidden @ ( B @ C ) )
          | ( A = B ) ) ) ) )).

thf('12',plain,(
    ! [X1017: $i,X1019: $i,X1020: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ ( X1017 @ X1019 ) @ X1020 ) )
        = ( k1_tarski @ X1017 ) )
      | ( X1017 != X1019 )
      | ( r2_hidden @ ( X1017 @ X1020 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('13',plain,(
    ! [X1019: $i,X1020: $i] :
      ( ( r2_hidden @ ( X1019 @ X1020 ) )
      | ( ( k4_xboole_0 @ ( k2_tarski @ ( X1019 @ X1019 ) @ X1020 ) )
        = ( k1_tarski @ X1019 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('14',plain,(
    ! [X175: $i,X176: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X175 @ X176 ) @ X175 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('15',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf('19',plain,(
    ! [X268: $i,X269: $i,X270: $i] :
      ( ( k3_xboole_0 @ ( X268 @ ( k4_xboole_0 @ ( X269 @ X270 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X268 @ X269 ) @ X270 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X104: $i,X105: $i] :
      ( ( k4_xboole_0 @ ( X104 @ X105 ) )
      = ( k5_xboole_0 @ ( X104 @ ( k3_xboole_0 @ ( X104 @ X105 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('23',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ k1_xboole_0 ) )
      = X302 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ o_0_0_xboole_0 ) )
      = X302 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( X1 @ ( k1_tarski @ X0 ) ) )
        = X1 )
      | ( r2_hidden @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != sk_A_2 )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != sk_A_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != sk_A_2 )
    | ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
 != sk_A_2 ),
    inference('sat_resolution*',[status(thm)],['2','9','29'])).

thf('31',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
 != sk_A_2 ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( sk_A_2 != sk_A_2 )
    | ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_B_2 @ sk_A_2 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['11','33'])).

%------------------------------------------------------------------------------
