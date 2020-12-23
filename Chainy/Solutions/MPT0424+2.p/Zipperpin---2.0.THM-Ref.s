%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0424+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2g42QvKuLE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 240 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_10_type,type,(
    sk_B_10: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_24_type,type,(
    sk_C_24: $i )).

thf(t56_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A @ B ) )
        & ( r2_hidden @ ( C @ A ) ) )
     => ( r1_tarski @ ( C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( k3_tarski @ A @ B ) )
          & ( r2_hidden @ ( C @ A ) ) )
       => ( r1_tarski @ ( C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( sk_C_24 @ sk_B_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_C_24 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( r1_tarski @ ( A @ ( k3_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1058: $i,X1059: $i] :
      ( ( r1_tarski @ ( X1058 @ ( k3_tarski @ X1059 ) ) )
      | ~ ( r2_hidden @ ( X1058 @ X1059 ) ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( sk_C_24 @ ( k3_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_tarski @ sk_A_2 @ sk_B_10 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('5',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('6',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_10 )
    | ( r2_xboole_0 @ ( k3_tarski @ sk_A_2 @ sk_B_10 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( sk_C_24 @ ( k3_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r2_xboole_0 @ ( B @ C ) ) )
     => ( r2_xboole_0 @ ( A @ C ) ) ) )).

thf('8',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ~ ( r1_tarski @ ( X94 @ X95 ) )
      | ~ ( r2_xboole_0 @ ( X95 @ X96 ) )
      | ( r2_xboole_0 @ ( X94 @ X96 ) ) ) ),
    inference(cnf,[status(esa)],[l58_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ ( sk_C_24 @ X0 ) )
      | ~ ( r2_xboole_0 @ ( k3_tarski @ sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_10 )
    | ( r2_xboole_0 @ ( sk_C_24 @ sk_B_10 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( X40 @ X41 ) )
      | ~ ( r2_xboole_0 @ ( X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('12',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_10 )
    | ( r1_tarski @ ( sk_C_24 @ sk_B_10 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ ( sk_C_24 @ sk_B_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k3_tarski @ sk_A_2 )
    = sk_B_10 ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( sk_C_24 @ sk_B_10 ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
