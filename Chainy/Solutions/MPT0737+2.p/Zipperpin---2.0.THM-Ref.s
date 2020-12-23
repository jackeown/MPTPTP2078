%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0737+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hc4UDt6b6S

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   34 (  48 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 ( 272 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(sk_A_13_type,type,(
    sk_A_13: $i )).

thf(sk_B_32_type,type,(
    sk_B_32: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(t25_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( r3_xboole_0 @ ( A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( r3_xboole_0 @ ( A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_ordinal1])).

thf('0',plain,(
    ~ ( r3_xboole_0 @ ( sk_A_13 @ sk_B_32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ ( A @ B ) )
        | ( r1_ordinal1 @ ( B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3066: $i,X3067: $i] :
      ( ~ ( v3_ordinal1 @ X3066 )
      | ~ ( v3_ordinal1 @ X3067 )
      | ( r1_ordinal1 @ ( X3066 @ X3067 ) )
      | ( r1_ordinal1 @ ( X3067 @ X3066 ) ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ( r1_ordinal1 @ ( sk_A_13 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ ( A @ B ) )
      <=> ( r1_tarski @ ( A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3080: $i,X3081: $i] :
      ( ~ ( v3_ordinal1 @ X3080 )
      | ~ ( v3_ordinal1 @ X3081 )
      | ( r1_tarski @ ( X3080 @ X3081 ) )
      | ~ ( r1_ordinal1 @ ( X3080 @ X3081 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_A_13 @ X0 ) )
      | ( r1_tarski @ ( X0 @ sk_A_13 ) )
      | ~ ( v3_ordinal1 @ sk_A_13 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_A_13 @ X0 ) )
      | ( r1_tarski @ ( X0 @ sk_A_13 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( X0 @ sk_A_13 ) )
      | ( r1_ordinal1 @ ( sk_A_13 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        | ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X82: $i,X83: $i] :
      ( ( r3_xboole_0 @ ( X82 @ X83 ) )
      | ~ ( r1_tarski @ ( X83 @ X82 ) ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_A_13 @ X0 ) )
      | ( r3_xboole_0 @ ( sk_A_13 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r3_xboole_0 @ ( sk_A_13 @ sk_B_32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_ordinal1 @ ( sk_A_13 @ sk_B_32 ) )
    | ~ ( v3_ordinal1 @ sk_B_32 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_B_32 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_ordinal1 @ ( sk_A_13 @ sk_B_32 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3080: $i,X3081: $i] :
      ( ~ ( v3_ordinal1 @ X3080 )
      | ~ ( v3_ordinal1 @ X3081 )
      | ( r1_tarski @ ( X3080 @ X3081 ) )
      | ~ ( r1_ordinal1 @ ( X3080 @ X3081 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('16',plain,
    ( ( r1_tarski @ ( sk_A_13 @ sk_B_32 ) )
    | ~ ( v3_ordinal1 @ sk_B_32 )
    | ~ ( v3_ordinal1 @ sk_A_13 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B_32 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( sk_A_13 @ sk_B_32 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X82: $i,X83: $i] :
      ( ( r3_xboole_0 @ ( X82 @ X83 ) )
      | ~ ( r1_tarski @ ( X82 @ X83 ) ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('21',plain,(
    r3_xboole_0 @ ( sk_A_13 @ sk_B_32 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
