%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0237+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BCKqlzkbkY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   81 (  81 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) )
        = ( k2_tarski @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) )
 != ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( A @ B ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X1006: $i,X1007: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( X1006 @ X1007 ) ) )
      = ( k2_xboole_0 @ ( X1006 @ X1007 ) ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
 != ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X702: $i,X703: $i] :
      ( ( k2_tarski @ ( X702 @ X703 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X702 @ ( k1_tarski @ X703 ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,(
    ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) )
 != ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
