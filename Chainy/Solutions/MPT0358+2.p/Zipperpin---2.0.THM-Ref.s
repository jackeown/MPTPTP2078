%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0358+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RhbI8Pnm4j

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 5.58s
% Output     : Refutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 133 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  355 ( 898 expanded)
%              Number of equality atoms :   46 ( 114 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( r1_tarski @ ( B @ ( k3_subset_1 @ ( A @ B ) ) ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( r1_tarski @ ( B @ ( k3_subset_1 @ ( A @ B ) ) ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B_8
      = ( k1_subset_1 @ sk_A_2 ) )
    | ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) )
   <= ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B_8
     != ( k1_subset_1 @ sk_A_2 ) )
    | ~ ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B_8
     != ( k1_subset_1 @ sk_A_2 ) )
    | ~ ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X1472: $i] :
      ( ( k1_subset_1 @ X1472 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X1472: $i] :
      ( ( k1_subset_1 @ X1472 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_8
      = ( k1_subset_1 @ sk_A_2 ) )
   <= ( sk_B_8
      = ( k1_subset_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( sk_B_8 = o_0_0_xboole_0 )
   <= ( sk_B_8
      = ( k1_subset_1 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) )
   <= ~ ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ o_0_0_xboole_0 ) ) ) )
   <= ( ~ ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) )
      & ( sk_B_8
        = ( k1_subset_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_8 = o_0_0_xboole_0 )
   <= ( sk_B_8
      = ( k1_subset_1 @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('12',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) )
    | ( sk_B_8
     != ( k1_subset_1 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) )
    | ( sk_B_8
      = ( k1_subset_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['3','15','16'])).

thf('18',plain,(
    r1_tarski @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('19',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) )
    = sk_B_8 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k4_xboole_0 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('23',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('26',plain,(
    ! [X359: $i,X360: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X359 @ X360 ) @ X360 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('27',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X359: $i,X360: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ ( X359 @ X360 ) @ X360 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ ( X1 @ X0 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    o_0_0_xboole_0 = sk_B_8 ),
    inference(demod,[status(thm)],['20','25','34'])).

thf('36',plain,
    ( ( sk_B_8
     != ( k1_subset_1 @ sk_A_2 ) )
   <= ( sk_B_8
     != ( k1_subset_1 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    ! [X1472: $i] :
      ( ( k1_subset_1 @ X1472 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('38',plain,
    ( ( sk_B_8 != o_0_0_xboole_0 )
   <= ( sk_B_8
     != ( k1_subset_1 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    sk_B_8
 != ( k1_subset_1 @ sk_A_2 ) ),
    inference('sat_resolution*',[status(thm)],['3','15'])).

thf('40',plain,(
    sk_B_8 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','40'])).

%------------------------------------------------------------------------------
