%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0320+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2TdULfUwfn

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  386 ( 601 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_13_type,type,(
    sk_C_13: $i )).

thf(t132_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( C @ ( k2_tarski @ ( A @ B ) ) ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ ( C @ ( k1_tarski @ B ) ) ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ ( A @ B ) @ C ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k2_zfmisc_1 @ ( C @ ( k2_tarski @ ( A @ B ) ) ) )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ ( C @ ( k1_tarski @ B ) ) ) ) ) )
        & ( ( k2_zfmisc_1 @ ( k2_tarski @ ( A @ B ) @ C ) )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_C_13 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) )
   <= ( ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( C @ ( k2_xboole_0 @ ( A @ B ) ) ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( C @ A ) @ ( k2_zfmisc_1 @ ( C @ B ) ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( A @ C ) @ ( k2_zfmisc_1 @ ( B @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X1107: $i,X1109: $i,X1110: $i] :
      ( ( k2_zfmisc_1 @ ( X1110 @ ( k2_xboole_0 @ ( X1107 @ X1109 ) ) ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( X1110 @ X1107 ) @ ( k2_zfmisc_1 @ ( X1110 @ X1109 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X702: $i,X703: $i] :
      ( ( k2_tarski @ ( X702 @ X703 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X702 @ ( k1_tarski @ X703 ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,
    ( ( ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
     != ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) )
   <= ( ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X1107: $i,X1108: $i,X1109: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( X1107 @ X1109 ) @ X1108 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( X1107 @ X1108 ) @ ( k2_zfmisc_1 @ ( X1109 @ X1108 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_C_13 ) ) ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_C_13 ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
     != ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) @ sk_C_13 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_C_13 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X702: $i,X703: $i] :
      ( ( k2_tarski @ ( X702 @ X703 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X702 @ ( k1_tarski @ X703 ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('10',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
     != ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_C_13 ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
    = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_C_13 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_13 ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_C_13 ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ( k2_zfmisc_1 @ ( sk_C_13 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['5','13'])).

%------------------------------------------------------------------------------
