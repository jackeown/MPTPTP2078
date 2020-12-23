%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0744+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QChQvlGVsH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 23.74s
% Output     : Refutation 23.74s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 170 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   19
%              Number of atoms          :  441 (1312 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_B_33_type,type,(
    sk_B_33: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(fc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( v1_xboole_0 @ ( k1_ordinal1 @ A ) )
        & ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X3084: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X3084 ) )
      | ~ ( v3_ordinal1 @ X3084 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ ( A @ B ) )
            | ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X3110: $i,X3111: $i] :
      ( ~ ( v3_ordinal1 @ X3110 )
      | ( r1_ordinal1 @ ( X3111 @ X3110 ) )
      | ( r2_hidden @ ( X3110 @ X3111 ) )
      | ~ ( v3_ordinal1 @ X3111 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ ( A @ ( k1_ordinal1 @ B ) ) )
          <=> ( r1_ordinal1 @ ( A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ ( A @ ( k1_ordinal1 @ B ) ) )
            <=> ( r1_ordinal1 @ ( A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('2',plain,
    ( ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
    | ~ ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) )
   <= ~ ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_33 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_33 @ sk_A_14 ) )
      | ~ ( v3_ordinal1 @ sk_A_14 ) )
   <= ~ ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v3_ordinal1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_33 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_33 @ sk_A_14 ) ) )
   <= ~ ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) )
    | ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(reflexivity_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( r1_ordinal1 @ ( A @ A ) ) ) )).

thf('8',plain,(
    ! [X3087: $i,X3088: $i] :
      ( ( r1_ordinal1 @ ( X3087 @ X3087 ) )
      | ~ ( v3_ordinal1 @ X3087 )
      | ~ ( v3_ordinal1 @ X3088 ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_ordinal1])).

thf('9',plain,
    ( ! [X3087: $i] :
        ( ( r1_ordinal1 @ ( X3087 @ X3087 ) )
        | ~ ( v3_ordinal1 @ X3087 ) )
   <= ! [X3087: $i] :
        ( ( r1_ordinal1 @ ( X3087 @ X3087 ) )
        | ~ ( v3_ordinal1 @ X3087 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ! [X3088: $i] :
        ~ ( v3_ordinal1 @ X3088 )
   <= ! [X3088: $i] :
        ~ ( v3_ordinal1 @ X3088 ) ),
    inference(split,[status(esa)],['8'])).

thf('12',plain,(
    ~ ! [X3088: $i] :
        ~ ( v3_ordinal1 @ X3088 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X3087: $i] :
        ( ( r1_ordinal1 @ ( X3087 @ X3087 ) )
        | ~ ( v3_ordinal1 @ X3087 ) )
    | ! [X3088: $i] :
        ~ ( v3_ordinal1 @ X3088 ) ),
    inference(split,[status(esa)],['8'])).

thf('14',plain,(
    ! [X3087: $i] :
      ( ( r1_ordinal1 @ ( X3087 @ X3087 ) )
      | ~ ( v3_ordinal1 @ X3087 ) ) ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3087: $i] :
      ( ( r1_ordinal1 @ ( X3087 @ X3087 ) )
      | ~ ( v3_ordinal1 @ X3087 ) ) ),
    inference(simpl_trail,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X3110: $i,X3111: $i] :
      ( ~ ( v3_ordinal1 @ X3110 )
      | ( r1_ordinal1 @ ( X3111 @ X3110 ) )
      | ( r2_hidden @ ( X3110 @ X3111 ) )
      | ~ ( v3_ordinal1 @ X3111 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('17',plain,
    ( ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
    | ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) )
   <= ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ ( k1_ordinal1 @ B ) ) )
    <=> ( ( r2_hidden @ ( A @ B ) )
        | ( A = B ) ) ) )).

thf('19',plain,(
    ! [X3092: $i,X3093: $i] :
      ( ( X3093 = X3092 )
      | ( r2_hidden @ ( X3093 @ X3092 ) )
      | ~ ( r2_hidden @ ( X3093 @ ( k1_ordinal1 @ X3092 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('20',plain,
    ( ( ( r2_hidden @ ( sk_A_14 @ sk_B_33 ) )
      | ( sk_A_14 = sk_B_33 ) )
   <= ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X0 @ X1 ) )
      | ~ ( r2_hidden @ ( X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('22',plain,
    ( ( ( sk_A_14 = sk_B_33 )
      | ~ ( r2_hidden @ ( sk_B_33 @ sk_A_14 ) ) )
   <= ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A_14 )
      | ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
      | ~ ( v3_ordinal1 @ sk_B_33 )
      | ( sk_A_14 = sk_B_33 ) )
   <= ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_ordinal1 @ sk_B_33 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
      | ( sk_A_14 = sk_B_33 ) )
   <= ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
   <= ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( sk_A_14 = sk_B_33 )
   <= ( ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
      & ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
   <= ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_A_14 ) )
   <= ( ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
      & ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v3_ordinal1 @ sk_A_14 )
   <= ( ~ ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
      & ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
    | ~ ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['7','33'])).

thf('35',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_33 ) )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_33 @ sk_A_14 ) ) ),
    inference(simpl_trail,[status(thm)],['6','34'])).

thf('36',plain,
    ( ~ ( v3_ordinal1 @ sk_B_33 )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_33 @ sk_A_14 ) ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_B_33 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_ordinal1 @ ( k1_ordinal1 @ sk_B_33 @ sk_A_14 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ ( A @ B ) )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A @ B ) ) ) ) ) )).

thf('39',plain,(
    ! [X3118: $i,X3119: $i] :
      ( ~ ( v3_ordinal1 @ X3118 )
      | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ X3119 @ X3118 ) )
      | ( r2_hidden @ ( X3119 @ X3118 ) )
      | ~ ( v3_ordinal1 @ X3119 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('40',plain,
    ( ~ ( v3_ordinal1 @ sk_B_33 )
    | ( r2_hidden @ ( sk_B_33 @ sk_A_14 ) )
    | ~ ( v3_ordinal1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_B_33 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_ordinal1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_hidden @ ( sk_B_33 @ sk_A_14 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) )).

thf('44',plain,(
    ! [X3138: $i,X3139: $i] :
      ( ~ ( r2_hidden @ ( X3138 @ X3139 ) )
      | ~ ( r1_tarski @ ( X3139 @ X3138 ) ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('45',plain,(
    ~ ( r1_tarski @ ( sk_A_14 @ sk_B_33 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
   <= ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) ) ),
    inference(split,[status(esa)],['17'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ ( A @ B ) )
      <=> ( r1_tarski @ ( A @ B ) ) ) ) )).

thf('47',plain,(
    ! [X3085: $i,X3086: $i] :
      ( ~ ( v3_ordinal1 @ X3085 )
      | ~ ( v3_ordinal1 @ X3086 )
      | ( r1_tarski @ ( X3085 @ X3086 ) )
      | ~ ( r1_ordinal1 @ ( X3085 @ X3086 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('48',plain,
    ( ( ( r1_tarski @ ( sk_A_14 @ sk_B_33 ) )
      | ~ ( v3_ordinal1 @ sk_B_33 )
      | ~ ( v3_ordinal1 @ sk_A_14 ) )
   <= ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_B_33 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_ordinal1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tarski @ ( sk_A_14 @ sk_B_33 ) )
   <= ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) )
    | ( r2_hidden @ ( sk_A_14 @ ( k1_ordinal1 @ sk_B_33 ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('53',plain,(
    r1_ordinal1 @ ( sk_A_14 @ sk_B_33 ) ),
    inference('sat_resolution*',[status(thm)],['7','33','52'])).

thf('54',plain,(
    r1_tarski @ ( sk_A_14 @ sk_B_33 ) ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['45','54'])).

%------------------------------------------------------------------------------
