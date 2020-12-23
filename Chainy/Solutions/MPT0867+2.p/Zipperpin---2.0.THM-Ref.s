%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0867+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NwSUpq3g7v

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 12.89s
% Output     : Refutation 12.89s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :  121 ( 121 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_73_type,type,(
    sk_B_73: $i )).

thf(sk_D_93_type,type,(
    sk_D_93: $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(t25_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( A @ B ) @ ( k2_tarski @ ( C @ D ) ) ) )
      = ( k2_enumset1 @ ( k4_tarski @ ( A @ C ) @ ( k4_tarski @ ( A @ D ) @ ( k4_tarski @ ( B @ C ) @ ( k4_tarski @ ( B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_zfmisc_1 @ ( k2_tarski @ ( A @ B ) @ ( k2_tarski @ ( C @ D ) ) ) )
        = ( k2_enumset1 @ ( k4_tarski @ ( A @ C ) @ ( k4_tarski @ ( A @ D ) @ ( k4_tarski @ ( B @ C ) @ ( k4_tarski @ ( B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_mcart_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_14 @ sk_B_73 ) @ ( k2_tarski @ ( sk_C_93 @ sk_D_93 ) ) ) )
 != ( k2_enumset1 @ ( k4_tarski @ ( sk_A_14 @ sk_C_93 ) @ ( k4_tarski @ ( sk_A_14 @ sk_D_93 ) @ ( k4_tarski @ ( sk_B_73 @ sk_C_93 ) @ ( k4_tarski @ ( sk_B_73 @ sk_D_93 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( A @ B ) @ ( k2_tarski @ ( C @ D ) ) ) )
      = ( k2_enumset1 @ ( k4_tarski @ ( A @ C ) @ ( k4_tarski @ ( A @ D ) @ ( k4_tarski @ ( B @ C ) @ ( k4_tarski @ ( B @ D ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X1222: $i,X1223: $i,X1224: $i,X1225: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( X1222 @ X1225 ) @ ( k2_tarski @ ( X1223 @ X1224 ) ) ) )
      = ( k2_enumset1 @ ( k4_tarski @ ( X1222 @ X1223 ) @ ( k4_tarski @ ( X1222 @ X1224 ) @ ( k4_tarski @ ( X1225 @ X1223 ) @ ( k4_tarski @ ( X1225 @ X1224 ) ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('2',plain,(
    ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_14 @ sk_B_73 ) @ ( k2_tarski @ ( sk_C_93 @ sk_D_93 ) ) ) )
 != ( k2_zfmisc_1 @ ( k2_tarski @ ( sk_A_14 @ sk_B_73 ) @ ( k2_tarski @ ( sk_C_93 @ sk_D_93 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    $false ),
    inference(simplify,[status(thm)],['2'])).

%------------------------------------------------------------------------------
