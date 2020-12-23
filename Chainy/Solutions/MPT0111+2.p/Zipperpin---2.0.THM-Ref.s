%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0111+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IqJ6Y7Uiuz

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 115 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  370 ( 967 expanded)
%              Number of equality atoms :   24 (  66 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(reflexivity_r3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( r3_xboole_0 @ ( A @ A ) ) )).

thf('0',plain,(
    ! [X101: $i] :
      ( r3_xboole_0 @ ( X101 @ X101 ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_xboole_0])).

thf(t104_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( ~ ( r2_xboole_0 @ ( A @ B ) )
          & ( A != B )
          & ~ ( r2_xboole_0 @ ( B @ A ) ) )
    <=> ( r3_xboole_0 @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( ~ ( r2_xboole_0 @ ( A @ B ) )
            & ( A != B )
            & ~ ( r2_xboole_0 @ ( B @ A ) ) )
      <=> ( r3_xboole_0 @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t104_xboole_1])).

thf('1',plain,
    ( ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    | ( sk_A_2 = sk_B_2 )
    | ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A_2 = sk_B_2 )
   <= ( sk_A_2 = sk_B_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
   <= ( ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      & ( sk_A_2 = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( sk_A_2 != sk_B_2 )
    | ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,
    ( ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('8',plain,
    ( ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('9',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( X40 @ X41 ) )
      | ~ ( r2_xboole_0 @ ( X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('10',plain,
    ( ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        | ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X82: $i,X83: $i] :
      ( ( r3_xboole_0 @ ( X82 @ X83 ) )
      | ~ ( r1_tarski @ ( X82 @ X83 ) ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('12',plain,
    ( ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ( sk_A_2 != sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A_2 != sk_B_2 )
    | ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    | ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('20',plain,(
    ! [X81: $i,X82: $i] :
      ( ( r1_tarski @ ( X81 @ X82 ) )
      | ( r1_tarski @ ( X82 @ X81 ) )
      | ~ ( r3_xboole_0 @ ( X82 @ X81 ) ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('21',plain,
    ( ( ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
      | ( r1_tarski @ ( sk_B_2 @ sk_A_2 ) ) )
   <= ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('23',plain,
    ( ( ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
      | ( sk_B_2 = sk_A_2 )
      | ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) )
   <= ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('25',plain,
    ( ( ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
      | ( sk_B_2 = sk_A_2 )
      | ( sk_A_2 = sk_B_2 )
      | ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) )
   <= ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      | ( sk_B_2 = sk_A_2 )
      | ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) )
   <= ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,
    ( ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('29',plain,(
    ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['7','28'])).

thf('30',plain,(
    ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,
    ( ( ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
      | ( sk_B_2 = sk_A_2 ) )
   <= ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf('32',plain,
    ( ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
   <= ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('33',plain,
    ( ( sk_B_2 = sk_A_2 )
   <= ( ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
      & ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A_2 != sk_B_2 )
   <= ( sk_A_2 != sk_B_2 ) ),
    inference(split,[status(esa)],['15'])).

thf('35',plain,
    ( ( sk_A_2 != sk_A_2 )
   <= ( ( sk_A_2 != sk_B_2 )
      & ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
      & ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    | ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ( sk_A_2 = sk_B_2 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    | ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ( r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ( sk_A_2 = sk_B_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('38',plain,
    ( ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
   <= ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('39',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( X40 @ X41 ) )
      | ~ ( r2_xboole_0 @ ( X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('40',plain,
    ( ( r1_tarski @ ( sk_B_2 @ sk_A_2 ) )
   <= ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X82: $i,X83: $i] :
      ( ( r3_xboole_0 @ ( X82 @ X83 ) )
      | ~ ( r1_tarski @ ( X83 @ X82 ) ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('42',plain,
    ( ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,
    ( ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    | ( r3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['6','7','14','16','18','36','37','44'])).

%------------------------------------------------------------------------------
