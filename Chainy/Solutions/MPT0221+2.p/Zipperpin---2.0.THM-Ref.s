%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0221+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LmJRGu96Ng

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 (  92 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t16_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
        & ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r1_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
          & ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t16_zfmisc_1])).

thf('0',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_A_2 = sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ ( A @ A ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ A ) )
          & ( A = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X319: $i] :
      ( ( X319 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X319 @ X319 ) ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X319: $i] :
      ( ( X319 = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X319 @ X319 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_tarski @ sk_A_2 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X972: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X972 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
