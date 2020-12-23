%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0230+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AzR5cPlYVv

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 214 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_8_type,type,(
    sk_C_8: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A @ ( k2_tarski @ ( B @ C ) ) ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A @ ( k2_tarski @ ( B @ C ) ) ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_8 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = k1_xboole_0 )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X990: $i,X991: $i] :
      ( ( r2_hidden @ ( X990 @ X991 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X990 @ X991 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X990: $i,X991: $i] :
      ( ( r2_hidden @ ( X990 @ X991 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X990 @ X991 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_8 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r2_hidden @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_8 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('10',plain,(
    ! [X441: $i,X443: $i,X444: $i,X445: $i] :
      ( ~ ( r2_hidden @ ( X445 @ X443 ) )
      | ( X445 = X444 )
      | ( X445 = X441 )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('11',plain,(
    ! [X441: $i,X444: $i,X445: $i] :
      ( ( X445 = X441 )
      | ( X445 = X444 )
      | ~ ( r2_hidden @ ( X445 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_A_2 = sk_B_2 )
    | ( sk_A_2 = sk_C_8 ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    sk_A_2 != sk_C_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_A_2 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13','14'])).

%------------------------------------------------------------------------------
