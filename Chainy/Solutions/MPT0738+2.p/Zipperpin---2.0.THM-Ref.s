%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0738+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XCuUiUBq9n

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 126 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :   21
%              Number of atoms          :  435 ( 912 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_32_type,type,(
    sk_B_32: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_13_type,type,(
    sk_A_13: $i )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(t26_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ ( A @ B ) )
            | ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r1_ordinal1 @ ( A @ B ) )
              | ( r2_hidden @ ( B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_ordinal1])).

thf('0',plain,(
    ~ ( r1_ordinal1 @ ( sk_A_13 @ sk_B_32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v3_ordinal1 @ sk_B_32 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( r3_xboole_0 @ ( A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X3103: $i,X3104: $i] :
      ( ~ ( v3_ordinal1 @ X3103 )
      | ( r3_xboole_0 @ ( X3104 @ X3103 ) )
      | ~ ( v3_ordinal1 @ X3104 ) ) ),
    inference(cnf,[status(esa)],[t25_ordinal1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r3_xboole_0 @ ( X0 @ sk_B_32 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        | ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X81: $i,X82: $i] :
      ( ( r1_tarski @ ( X81 @ X82 ) )
      | ( r1_tarski @ ( X82 @ X81 ) )
      | ~ ( r3_xboole_0 @ ( X82 @ X81 ) ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( X0 @ sk_B_32 ) )
      | ( r1_tarski @ ( sk_B_32 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X3103: $i,X3104: $i] :
      ( ~ ( v3_ordinal1 @ X3103 )
      | ( r3_xboole_0 @ ( X3104 @ X3103 ) )
      | ~ ( v3_ordinal1 @ X3104 ) ) ),
    inference(cnf,[status(esa)],[t25_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r3_xboole_0 @ ( X0 @ sk_A_13 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X81: $i,X82: $i] :
      ( ( r1_tarski @ ( X81 @ X82 ) )
      | ( r1_tarski @ ( X82 @ X81 ) )
      | ~ ( r3_xboole_0 @ ( X82 @ X81 ) ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( X0 @ sk_A_13 ) )
      | ( r1_tarski @ ( sk_A_13 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ ( A @ B ) )
      <=> ( r1_tarski @ ( A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X3080: $i,X3081: $i] :
      ( ~ ( v3_ordinal1 @ X3080 )
      | ~ ( v3_ordinal1 @ X3081 )
      | ( r1_ordinal1 @ ( X3080 @ X3081 ) )
      | ~ ( r1_tarski @ ( X3080 @ X3081 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_A_13 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ~ ( v3_ordinal1 @ sk_A_13 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_A_13 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_A_13 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ~ ( r1_tarski @ ( X0 @ sk_A_13 ) )
      | ( X0 = sk_A_13 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( sk_A_13 @ sk_B_32 ) )
    | ~ ( v3_ordinal1 @ sk_A_13 )
    | ( sk_B_32 = sk_A_13 )
    | ( r1_ordinal1 @ ( sk_B_32 @ sk_A_13 ) )
    | ~ ( v3_ordinal1 @ sk_B_32 ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_ordinal1 @ sk_B_32 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ ( sk_A_13 @ sk_B_32 ) )
    | ( sk_B_32 = sk_A_13 )
    | ( r1_ordinal1 @ ( sk_B_32 @ sk_A_13 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X3080: $i,X3081: $i] :
      ( ~ ( v3_ordinal1 @ X3080 )
      | ~ ( v3_ordinal1 @ X3081 )
      | ( r1_ordinal1 @ ( X3080 @ X3081 ) )
      | ~ ( r1_tarski @ ( X3080 @ X3081 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('23',plain,
    ( ( r1_ordinal1 @ ( sk_B_32 @ sk_A_13 ) )
    | ( sk_B_32 = sk_A_13 )
    | ( r1_ordinal1 @ ( sk_A_13 @ sk_B_32 ) )
    | ~ ( v3_ordinal1 @ sk_B_32 )
    | ~ ( v3_ordinal1 @ sk_A_13 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_B_32 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_ordinal1 @ ( sk_B_32 @ sk_A_13 ) )
    | ( sk_B_32 = sk_A_13 )
    | ( r1_ordinal1 @ ( sk_A_13 @ sk_B_32 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( r1_ordinal1 @ ( sk_A_13 @ sk_B_32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B_32 = sk_A_13 )
    | ( r1_ordinal1 @ ( sk_B_32 @ sk_A_13 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3080: $i,X3081: $i] :
      ( ~ ( v3_ordinal1 @ X3080 )
      | ~ ( v3_ordinal1 @ X3081 )
      | ( r1_tarski @ ( X3080 @ X3081 ) )
      | ~ ( r1_ordinal1 @ ( X3080 @ X3081 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('30',plain,
    ( ( sk_B_32 = sk_A_13 )
    | ( r1_tarski @ ( sk_B_32 @ sk_A_13 ) )
    | ~ ( v3_ordinal1 @ sk_A_13 )
    | ~ ( v3_ordinal1 @ sk_B_32 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_ordinal1 @ sk_B_32 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_B_32 = sk_A_13 )
    | ( r1_tarski @ ( sk_B_32 @ sk_A_13 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('34',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('35',plain,
    ( ( sk_B_32 = sk_A_13 )
    | ( sk_B_32 = sk_A_13 )
    | ( r2_xboole_0 @ ( sk_B_32 @ sk_A_13 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_xboole_0 @ ( sk_B_32 @ sk_A_13 ) )
    | ( sk_B_32 = sk_A_13 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ ( A @ B ) )
           => ( r2_hidden @ ( A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X3094: $i,X3095: $i] :
      ( ~ ( v3_ordinal1 @ X3094 )
      | ( r2_hidden @ ( X3095 @ X3094 ) )
      | ~ ( r2_xboole_0 @ ( X3095 @ X3094 ) )
      | ~ ( v1_ordinal1 @ X3095 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('38',plain,
    ( ( sk_B_32 = sk_A_13 )
    | ~ ( v1_ordinal1 @ sk_B_32 )
    | ( r2_hidden @ ( sk_B_32 @ sk_A_13 ) )
    | ~ ( v3_ordinal1 @ sk_A_13 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_B_32 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('40',plain,(
    ! [X3064: $i] :
      ( ( v1_ordinal1 @ X3064 )
      | ~ ( v3_ordinal1 @ X3064 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('41',plain,(
    v1_ordinal1 @ sk_B_32 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_B_32 = sk_A_13 )
    | ( r2_hidden @ ( sk_B_32 @ sk_A_13 ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ ( sk_B_32 @ sk_A_13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_B_32 = sk_A_13 ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_A_13 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('47',plain,(
    ! [X3080: $i,X3081: $i] :
      ( ~ ( v3_ordinal1 @ X3080 )
      | ~ ( v3_ordinal1 @ X3081 )
      | ( r1_ordinal1 @ ( X3080 @ X3081 ) )
      | ~ ( r1_tarski @ ( X3080 @ X3081 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ( r1_ordinal1 @ ( sk_A_13 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ sk_A_13 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ( r1_ordinal1 @ ( sk_A_13 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_A_13 @ X0 ) )
      | ( r1_ordinal1 @ ( X0 @ sk_A_13 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( v3_ordinal1 @ sk_A_13 )
    | ( r1_ordinal1 @ ( sk_A_13 @ sk_A_13 ) ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_ordinal1 @ ( sk_A_13 @ sk_A_13 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45','54'])).

%------------------------------------------------------------------------------
