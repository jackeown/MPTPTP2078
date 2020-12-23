%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2VKMaPWfYw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:57 EST 2020

% Result     : Theorem 22.62s
% Output     : Refutation 22.62s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 839 expanded)
%              Number of leaves         :   25 ( 247 expanded)
%              Depth                    :   23
%              Number of atoms          : 1147 (6981 expanded)
%              Number of equality atoms :   35 ( 118 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X40 @ X41 ) )
      = ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('3',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('12',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','20'])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('24',plain,(
    ! [X50: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X50 ) )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('25',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('27',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('34',plain,(
    ! [X44: $i] :
      ( ( k1_ordinal1 @ X44 )
      = ( k2_xboole_0 @ X44 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('36',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X49 @ X48 )
      | ( r2_hidden @ X48 @ X49 )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('48',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X49 @ X48 )
      | ( r2_hidden @ X48 @ X49 )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf('54',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('59',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,
    ( ( ~ ( r1_tarski @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('67',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X50: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X50 ) )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('71',plain,(
    ! [X50: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X50 ) )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('72',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_ordinal1 @ X42 @ X43 )
      | ( r1_ordinal1 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('80',plain,(
    ! [X47: $i] :
      ( r2_hidden @ X47 @ ( k1_ordinal1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('81',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('82',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','83'])).

thf('85',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_ordinal1 @ sk_A @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('88',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','90'])).

thf('92',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('95',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('97',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['97','99'])).

thf('101',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('102',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['23','100','101'])).

thf('103',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['21','102'])).

thf('104',plain,(
    ! [X50: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X50 ) )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('105',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X49 @ X48 )
      | ( r2_hidden @ X48 @ X49 )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('106',plain,(
    ! [X44: $i] :
      ( ( k1_ordinal1 @ X44 )
      = ( k2_xboole_0 @ X44 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('107',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('108',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf('119',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['23','100'])).

thf('120',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['118','119'])).

thf('121',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('123',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('125',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('126',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('127',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ~ ( v3_ordinal1 @ X46 )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( r1_ordinal1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('132',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['23','100','101'])).

thf('137',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['135','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['123','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2VKMaPWfYw
% 0.09/0.29  % Computer   : n024.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 20:59:21 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  % Running portfolio for 600 s
% 0.09/0.29  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.09/0.29  % Number of cores: 8
% 0.09/0.29  % Python version: Python 3.6.8
% 0.09/0.29  % Running in FO mode
% 22.62/22.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 22.62/22.81  % Solved by: fo/fo7.sh
% 22.62/22.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.62/22.81  % done 27645 iterations in 22.451s
% 22.62/22.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 22.62/22.81  % SZS output start Refutation
% 22.62/22.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 22.62/22.81  thf(sk_A_type, type, sk_A: $i).
% 22.62/22.81  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 22.62/22.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 22.62/22.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 22.62/22.81  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 22.62/22.81  thf(sk_B_type, type, sk_B: $i).
% 22.62/22.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 22.62/22.81  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 22.62/22.81  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 22.62/22.81  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 22.62/22.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 22.62/22.81  thf(t69_enumset1, axiom,
% 22.62/22.81    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 22.62/22.81  thf('0', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 22.62/22.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 22.62/22.81  thf(l51_zfmisc_1, axiom,
% 22.62/22.81    (![A:$i,B:$i]:
% 22.62/22.81     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 22.62/22.81  thf('1', plain,
% 22.62/22.81      (![X40 : $i, X41 : $i]:
% 22.62/22.81         ((k3_tarski @ (k2_tarski @ X40 @ X41)) = (k2_xboole_0 @ X40 @ X41))),
% 22.62/22.81      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 22.62/22.81  thf('2', plain,
% 22.62/22.81      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 22.62/22.81      inference('sup+', [status(thm)], ['0', '1'])).
% 22.62/22.81  thf(t33_ordinal1, conjecture,
% 22.62/22.81    (![A:$i]:
% 22.62/22.81     ( ( v3_ordinal1 @ A ) =>
% 22.62/22.81       ( ![B:$i]:
% 22.62/22.81         ( ( v3_ordinal1 @ B ) =>
% 22.62/22.81           ( ( r2_hidden @ A @ B ) <=>
% 22.62/22.81             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 22.62/22.81  thf(zf_stmt_0, negated_conjecture,
% 22.62/22.81    (~( ![A:$i]:
% 22.62/22.81        ( ( v3_ordinal1 @ A ) =>
% 22.62/22.81          ( ![B:$i]:
% 22.62/22.81            ( ( v3_ordinal1 @ B ) =>
% 22.62/22.81              ( ( r2_hidden @ A @ B ) <=>
% 22.62/22.81                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 22.62/22.81    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 22.62/22.81  thf('3', plain,
% 22.62/22.81      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('4', plain,
% 22.62/22.81      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('split', [status(esa)], ['3'])).
% 22.62/22.81  thf(d3_xboole_0, axiom,
% 22.62/22.81    (![A:$i,B:$i,C:$i]:
% 22.62/22.81     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 22.62/22.81       ( ![D:$i]:
% 22.62/22.81         ( ( r2_hidden @ D @ C ) <=>
% 22.62/22.81           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 22.62/22.81  thf('5', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X0 @ X1)
% 22.62/22.81          | (r2_hidden @ X0 @ X2)
% 22.62/22.81          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 22.62/22.81      inference('cnf', [status(esa)], [d3_xboole_0])).
% 22.62/22.81  thf('6', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i, X3 : $i]:
% 22.62/22.81         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 22.62/22.81      inference('simplify', [status(thm)], ['5'])).
% 22.62/22.81  thf('7', plain,
% 22.62/22.81      ((![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))
% 22.62/22.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['4', '6'])).
% 22.62/22.81  thf('8', plain,
% 22.62/22.81      (((r2_hidden @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B))))
% 22.62/22.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup+', [status(thm)], ['2', '7'])).
% 22.62/22.81  thf(l1_zfmisc_1, axiom,
% 22.62/22.81    (![A:$i,B:$i]:
% 22.62/22.81     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 22.62/22.81  thf('9', plain,
% 22.62/22.81      (![X37 : $i, X39 : $i]:
% 22.62/22.81         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 22.62/22.81      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 22.62/22.81  thf('10', plain,
% 22.62/22.81      (((r1_tarski @ (k1_tarski @ sk_A) @ (k3_tarski @ (k1_tarski @ sk_B))))
% 22.62/22.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['8', '9'])).
% 22.62/22.81  thf('11', plain,
% 22.62/22.81      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 22.62/22.81      inference('sup+', [status(thm)], ['0', '1'])).
% 22.62/22.81  thf('12', plain,
% 22.62/22.81      (![X1 : $i, X3 : $i, X5 : $i]:
% 22.62/22.81         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 22.62/22.81          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 22.62/22.81          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 22.62/22.81          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 22.62/22.81      inference('cnf', [status(esa)], [d3_xboole_0])).
% 22.62/22.81  thf('13', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i]:
% 22.62/22.81         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 22.62/22.81          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 22.62/22.81          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 22.62/22.81      inference('eq_fact', [status(thm)], ['12'])).
% 22.62/22.81  thf('14', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 22.62/22.81          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 22.62/22.81      inference('eq_fact', [status(thm)], ['13'])).
% 22.62/22.81  thf('15', plain,
% 22.62/22.81      (![X1 : $i, X3 : $i, X5 : $i]:
% 22.62/22.81         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 22.62/22.81          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 22.62/22.81          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 22.62/22.81      inference('cnf', [status(esa)], [d3_xboole_0])).
% 22.62/22.81  thf('16', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 22.62/22.81          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 22.62/22.81          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['14', '15'])).
% 22.62/22.81  thf('17', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 22.62/22.81          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 22.62/22.81      inference('simplify', [status(thm)], ['16'])).
% 22.62/22.81  thf('18', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 22.62/22.81          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 22.62/22.81      inference('eq_fact', [status(thm)], ['13'])).
% 22.62/22.81  thf('19', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 22.62/22.81      inference('clc', [status(thm)], ['17', '18'])).
% 22.62/22.81  thf('20', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 22.62/22.81      inference('demod', [status(thm)], ['11', '19'])).
% 22.62/22.81  thf('21', plain,
% 22.62/22.81      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 22.62/22.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['10', '20'])).
% 22.62/22.81  thf('22', plain,
% 22.62/22.81      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 22.62/22.81        | ~ (r2_hidden @ sk_A @ sk_B))),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('23', plain,
% 22.62/22.81      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 22.62/22.81       ~ ((r2_hidden @ sk_A @ sk_B))),
% 22.62/22.81      inference('split', [status(esa)], ['22'])).
% 22.62/22.81  thf(t29_ordinal1, axiom,
% 22.62/22.81    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 22.62/22.81  thf('24', plain,
% 22.62/22.81      (![X50 : $i]:
% 22.62/22.81         ((v3_ordinal1 @ (k1_ordinal1 @ X50)) | ~ (v3_ordinal1 @ X50))),
% 22.62/22.81      inference('cnf', [status(esa)], [t29_ordinal1])).
% 22.62/22.81  thf('25', plain,
% 22.62/22.81      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('split', [status(esa)], ['3'])).
% 22.62/22.81  thf(redefinition_r1_ordinal1, axiom,
% 22.62/22.81    (![A:$i,B:$i]:
% 22.62/22.81     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 22.62/22.81       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 22.62/22.81  thf('26', plain,
% 22.62/22.81      (![X45 : $i, X46 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X45)
% 22.62/22.81          | ~ (v3_ordinal1 @ X46)
% 22.62/22.81          | (r1_tarski @ X45 @ X46)
% 22.62/22.81          | ~ (r1_ordinal1 @ X45 @ X46))),
% 22.62/22.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 22.62/22.81  thf('27', plain,
% 22.62/22.81      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_B)
% 22.62/22.81         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['25', '26'])).
% 22.62/22.81  thf('28', plain, ((v3_ordinal1 @ sk_B)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('29', plain,
% 22.62/22.81      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 22.62/22.81         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['27', '28'])).
% 22.62/22.81  thf('30', plain,
% 22.62/22.81      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['24', '29'])).
% 22.62/22.81  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('32', plain,
% 22.62/22.81      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['30', '31'])).
% 22.62/22.81  thf('33', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 22.62/22.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 22.62/22.81  thf(d1_ordinal1, axiom,
% 22.62/22.81    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 22.62/22.81  thf('34', plain,
% 22.62/22.81      (![X44 : $i]:
% 22.62/22.81         ((k1_ordinal1 @ X44) = (k2_xboole_0 @ X44 @ (k1_tarski @ X44)))),
% 22.62/22.81      inference('cnf', [status(esa)], [d1_ordinal1])).
% 22.62/22.81  thf('35', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 22.62/22.81      inference('sup+', [status(thm)], ['33', '34'])).
% 22.62/22.81  thf(t26_ordinal1, axiom,
% 22.62/22.81    (![A:$i]:
% 22.62/22.81     ( ( v3_ordinal1 @ A ) =>
% 22.62/22.81       ( ![B:$i]:
% 22.62/22.81         ( ( v3_ordinal1 @ B ) =>
% 22.62/22.81           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 22.62/22.81  thf('36', plain,
% 22.62/22.81      (![X48 : $i, X49 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X48)
% 22.62/22.81          | (r1_ordinal1 @ X49 @ X48)
% 22.62/22.81          | (r2_hidden @ X48 @ X49)
% 22.62/22.81          | ~ (v3_ordinal1 @ X49))),
% 22.62/22.81      inference('cnf', [status(esa)], [t26_ordinal1])).
% 22.62/22.81  thf('37', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X0 @ X3)
% 22.62/22.81          | (r2_hidden @ X0 @ X2)
% 22.62/22.81          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 22.62/22.81      inference('cnf', [status(esa)], [d3_xboole_0])).
% 22.62/22.81  thf('38', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i, X3 : $i]:
% 22.62/22.81         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 22.62/22.81      inference('simplify', [status(thm)], ['37'])).
% 22.62/22.81  thf('39', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X0)
% 22.62/22.81          | (r1_ordinal1 @ X0 @ X1)
% 22.62/22.81          | ~ (v3_ordinal1 @ X1)
% 22.62/22.81          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['36', '38'])).
% 22.62/22.81  thf('40', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i]:
% 22.62/22.81         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 22.62/22.81          | ~ (v3_ordinal1 @ X1)
% 22.62/22.81          | (r1_ordinal1 @ X0 @ X1)
% 22.62/22.81          | ~ (v3_ordinal1 @ X0))),
% 22.62/22.81      inference('sup+', [status(thm)], ['35', '39'])).
% 22.62/22.81  thf(t7_ordinal1, axiom,
% 22.62/22.81    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 22.62/22.81  thf('41', plain,
% 22.62/22.81      (![X51 : $i, X52 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 22.62/22.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 22.62/22.81  thf('42', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X0)
% 22.62/22.81          | (r1_ordinal1 @ X0 @ X1)
% 22.62/22.81          | ~ (v3_ordinal1 @ X1)
% 22.62/22.81          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 22.62/22.81      inference('sup-', [status(thm)], ['40', '41'])).
% 22.62/22.81  thf('43', plain,
% 22.62/22.81      (((~ (v3_ordinal1 @ sk_B)
% 22.62/22.81         | (r1_ordinal1 @ sk_A @ sk_B)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_A)))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['32', '42'])).
% 22.62/22.81  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('46', plain,
% 22.62/22.81      (((r1_ordinal1 @ sk_A @ sk_B))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['43', '44', '45'])).
% 22.62/22.81  thf('47', plain,
% 22.62/22.81      (![X45 : $i, X46 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X45)
% 22.62/22.81          | ~ (v3_ordinal1 @ X46)
% 22.62/22.81          | (r1_tarski @ X45 @ X46)
% 22.62/22.81          | ~ (r1_ordinal1 @ X45 @ X46))),
% 22.62/22.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 22.62/22.81  thf('48', plain,
% 22.62/22.81      ((((r1_tarski @ sk_A @ sk_B)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_B)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_A)))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['46', '47'])).
% 22.62/22.81  thf('49', plain, ((v3_ordinal1 @ sk_B)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('51', plain,
% 22.62/22.81      (((r1_tarski @ sk_A @ sk_B))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['48', '49', '50'])).
% 22.62/22.81  thf('52', plain,
% 22.62/22.81      (![X48 : $i, X49 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X48)
% 22.62/22.81          | (r1_ordinal1 @ X49 @ X48)
% 22.62/22.81          | (r2_hidden @ X48 @ X49)
% 22.62/22.81          | ~ (v3_ordinal1 @ X49))),
% 22.62/22.81      inference('cnf', [status(esa)], [t26_ordinal1])).
% 22.62/22.81  thf('53', plain,
% 22.62/22.81      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('split', [status(esa)], ['22'])).
% 22.62/22.81  thf('54', plain,
% 22.62/22.81      (((~ (v3_ordinal1 @ sk_B)
% 22.62/22.81         | (r1_ordinal1 @ sk_B @ sk_A)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['52', '53'])).
% 22.62/22.81  thf('55', plain, ((v3_ordinal1 @ sk_B)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('56', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('57', plain,
% 22.62/22.81      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['54', '55', '56'])).
% 22.62/22.81  thf('58', plain,
% 22.62/22.81      (![X45 : $i, X46 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X45)
% 22.62/22.81          | ~ (v3_ordinal1 @ X46)
% 22.62/22.81          | (r1_tarski @ X45 @ X46)
% 22.62/22.81          | ~ (r1_ordinal1 @ X45 @ X46))),
% 22.62/22.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 22.62/22.81  thf('59', plain,
% 22.62/22.81      ((((r1_tarski @ sk_B @ sk_A)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_A)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['57', '58'])).
% 22.62/22.81  thf('60', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('61', plain, ((v3_ordinal1 @ sk_B)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('62', plain,
% 22.62/22.81      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['59', '60', '61'])).
% 22.62/22.81  thf(d10_xboole_0, axiom,
% 22.62/22.81    (![A:$i,B:$i]:
% 22.62/22.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 22.62/22.81  thf('63', plain,
% 22.62/22.81      (![X6 : $i, X8 : $i]:
% 22.62/22.81         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 22.62/22.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 22.62/22.81  thf('64', plain,
% 22.62/22.81      (((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 22.62/22.81         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['62', '63'])).
% 22.62/22.81  thf('65', plain,
% 22.62/22.81      ((((sk_A) = (sk_B)))
% 22.62/22.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 22.62/22.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['51', '64'])).
% 22.62/22.81  thf('66', plain,
% 22.62/22.81      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['30', '31'])).
% 22.62/22.81  thf('67', plain,
% 22.62/22.81      (![X6 : $i, X8 : $i]:
% 22.62/22.81         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 22.62/22.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 22.62/22.81  thf('68', plain,
% 22.62/22.81      (((~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 22.62/22.81         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 22.62/22.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['66', '67'])).
% 22.62/22.81  thf('69', plain,
% 22.62/22.81      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 22.62/22.81         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 22.62/22.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 22.62/22.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['65', '68'])).
% 22.62/22.81  thf('70', plain,
% 22.62/22.81      (![X50 : $i]:
% 22.62/22.81         ((v3_ordinal1 @ (k1_ordinal1 @ X50)) | ~ (v3_ordinal1 @ X50))),
% 22.62/22.81      inference('cnf', [status(esa)], [t29_ordinal1])).
% 22.62/22.81  thf('71', plain,
% 22.62/22.81      (![X50 : $i]:
% 22.62/22.81         ((v3_ordinal1 @ (k1_ordinal1 @ X50)) | ~ (v3_ordinal1 @ X50))),
% 22.62/22.81      inference('cnf', [status(esa)], [t29_ordinal1])).
% 22.62/22.81  thf('72', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf(connectedness_r1_ordinal1, axiom,
% 22.62/22.81    (![A:$i,B:$i]:
% 22.62/22.81     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 22.62/22.81       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 22.62/22.81  thf('73', plain,
% 22.62/22.81      (![X42 : $i, X43 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X42)
% 22.62/22.81          | ~ (v3_ordinal1 @ X43)
% 22.62/22.81          | (r1_ordinal1 @ X42 @ X43)
% 22.62/22.81          | (r1_ordinal1 @ X43 @ X42))),
% 22.62/22.81      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 22.62/22.81  thf('74', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         ((r1_ordinal1 @ X0 @ sk_A)
% 22.62/22.81          | (r1_ordinal1 @ sk_A @ X0)
% 22.62/22.81          | ~ (v3_ordinal1 @ X0))),
% 22.62/22.81      inference('sup-', [status(thm)], ['72', '73'])).
% 22.62/22.81  thf('75', plain,
% 22.62/22.81      (![X45 : $i, X46 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X45)
% 22.62/22.81          | ~ (v3_ordinal1 @ X46)
% 22.62/22.81          | (r1_tarski @ X45 @ X46)
% 22.62/22.81          | ~ (r1_ordinal1 @ X45 @ X46))),
% 22.62/22.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 22.62/22.81  thf('76', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X0)
% 22.62/22.81          | (r1_ordinal1 @ sk_A @ X0)
% 22.62/22.81          | (r1_tarski @ X0 @ sk_A)
% 22.62/22.81          | ~ (v3_ordinal1 @ sk_A)
% 22.62/22.81          | ~ (v3_ordinal1 @ X0))),
% 22.62/22.81      inference('sup-', [status(thm)], ['74', '75'])).
% 22.62/22.81  thf('77', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('78', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X0)
% 22.62/22.81          | (r1_ordinal1 @ sk_A @ X0)
% 22.62/22.81          | (r1_tarski @ X0 @ sk_A)
% 22.62/22.81          | ~ (v3_ordinal1 @ X0))),
% 22.62/22.81      inference('demod', [status(thm)], ['76', '77'])).
% 22.62/22.81  thf('79', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         ((r1_tarski @ X0 @ sk_A)
% 22.62/22.81          | (r1_ordinal1 @ sk_A @ X0)
% 22.62/22.81          | ~ (v3_ordinal1 @ X0))),
% 22.62/22.81      inference('simplify', [status(thm)], ['78'])).
% 22.62/22.81  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 22.62/22.81  thf('80', plain, (![X47 : $i]: (r2_hidden @ X47 @ (k1_ordinal1 @ X47))),
% 22.62/22.81      inference('cnf', [status(esa)], [t10_ordinal1])).
% 22.62/22.81  thf('81', plain,
% 22.62/22.81      (![X51 : $i, X52 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 22.62/22.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 22.62/22.81  thf('82', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 22.62/22.81      inference('sup-', [status(thm)], ['80', '81'])).
% 22.62/22.81  thf('83', plain,
% 22.62/22.81      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 22.62/22.81        | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['79', '82'])).
% 22.62/22.81  thf('84', plain,
% 22.62/22.81      ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['71', '83'])).
% 22.62/22.81  thf('85', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('86', plain, ((r1_ordinal1 @ sk_A @ (k1_ordinal1 @ sk_A))),
% 22.62/22.81      inference('demod', [status(thm)], ['84', '85'])).
% 22.62/22.81  thf('87', plain,
% 22.62/22.81      (![X45 : $i, X46 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X45)
% 22.62/22.81          | ~ (v3_ordinal1 @ X46)
% 22.62/22.81          | (r1_tarski @ X45 @ X46)
% 22.62/22.81          | ~ (r1_ordinal1 @ X45 @ X46))),
% 22.62/22.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 22.62/22.81  thf('88', plain,
% 22.62/22.81      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 22.62/22.81        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 22.62/22.81        | ~ (v3_ordinal1 @ sk_A))),
% 22.62/22.81      inference('sup-', [status(thm)], ['86', '87'])).
% 22.62/22.81  thf('89', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('90', plain,
% 22.62/22.81      (((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 22.62/22.81        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 22.62/22.81      inference('demod', [status(thm)], ['88', '89'])).
% 22.62/22.81  thf('91', plain,
% 22.62/22.81      ((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['70', '90'])).
% 22.62/22.81  thf('92', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('93', plain, ((r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))),
% 22.62/22.81      inference('demod', [status(thm)], ['91', '92'])).
% 22.62/22.81  thf('94', plain,
% 22.62/22.81      ((((sk_A) = (sk_B)))
% 22.62/22.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 22.62/22.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['51', '64'])).
% 22.62/22.81  thf('95', plain,
% 22.62/22.81      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 22.62/22.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 22.62/22.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['69', '93', '94'])).
% 22.62/22.81  thf('96', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 22.62/22.81      inference('sup-', [status(thm)], ['80', '81'])).
% 22.62/22.81  thf('97', plain,
% 22.62/22.81      ((~ (r1_tarski @ sk_A @ sk_A))
% 22.62/22.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 22.62/22.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['95', '96'])).
% 22.62/22.81  thf('98', plain,
% 22.62/22.81      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 22.62/22.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 22.62/22.81  thf('99', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 22.62/22.81      inference('simplify', [status(thm)], ['98'])).
% 22.62/22.81  thf('100', plain,
% 22.62/22.81      (((r2_hidden @ sk_A @ sk_B)) | 
% 22.62/22.81       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 22.62/22.81      inference('demod', [status(thm)], ['97', '99'])).
% 22.62/22.81  thf('101', plain,
% 22.62/22.81      (((r2_hidden @ sk_A @ sk_B)) | 
% 22.62/22.81       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 22.62/22.81      inference('split', [status(esa)], ['3'])).
% 22.62/22.81  thf('102', plain, (((r2_hidden @ sk_A @ sk_B))),
% 22.62/22.81      inference('sat_resolution*', [status(thm)], ['23', '100', '101'])).
% 22.62/22.81  thf('103', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 22.62/22.81      inference('simpl_trail', [status(thm)], ['21', '102'])).
% 22.62/22.81  thf('104', plain,
% 22.62/22.81      (![X50 : $i]:
% 22.62/22.81         ((v3_ordinal1 @ (k1_ordinal1 @ X50)) | ~ (v3_ordinal1 @ X50))),
% 22.62/22.81      inference('cnf', [status(esa)], [t29_ordinal1])).
% 22.62/22.81  thf('105', plain,
% 22.62/22.81      (![X48 : $i, X49 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X48)
% 22.62/22.81          | (r1_ordinal1 @ X49 @ X48)
% 22.62/22.81          | (r2_hidden @ X48 @ X49)
% 22.62/22.81          | ~ (v3_ordinal1 @ X49))),
% 22.62/22.81      inference('cnf', [status(esa)], [t26_ordinal1])).
% 22.62/22.81  thf('106', plain,
% 22.62/22.81      (![X44 : $i]:
% 22.62/22.81         ((k1_ordinal1 @ X44) = (k2_xboole_0 @ X44 @ (k1_tarski @ X44)))),
% 22.62/22.81      inference('cnf', [status(esa)], [d1_ordinal1])).
% 22.62/22.81  thf('107', plain,
% 22.62/22.81      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X4 @ X2)
% 22.62/22.81          | (r2_hidden @ X4 @ X3)
% 22.62/22.81          | (r2_hidden @ X4 @ X1)
% 22.62/22.81          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 22.62/22.81      inference('cnf', [status(esa)], [d3_xboole_0])).
% 22.62/22.81  thf('108', plain,
% 22.62/22.81      (![X1 : $i, X3 : $i, X4 : $i]:
% 22.62/22.81         ((r2_hidden @ X4 @ X1)
% 22.62/22.81          | (r2_hidden @ X4 @ X3)
% 22.62/22.81          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 22.62/22.81      inference('simplify', [status(thm)], ['107'])).
% 22.62/22.81  thf('109', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 22.62/22.81          | (r2_hidden @ X1 @ X0)
% 22.62/22.81          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['106', '108'])).
% 22.62/22.81  thf('110', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 22.62/22.81          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 22.62/22.81          | ~ (v3_ordinal1 @ X1)
% 22.62/22.81          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 22.62/22.81          | (r2_hidden @ X1 @ X0))),
% 22.62/22.81      inference('sup-', [status(thm)], ['105', '109'])).
% 22.62/22.81  thf('111', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X0)
% 22.62/22.81          | (r2_hidden @ X1 @ X0)
% 22.62/22.81          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 22.62/22.81          | ~ (v3_ordinal1 @ X1)
% 22.62/22.81          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 22.62/22.81      inference('sup-', [status(thm)], ['104', '110'])).
% 22.62/22.81  thf('112', plain,
% 22.62/22.81      (![X51 : $i, X52 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 22.62/22.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 22.62/22.81  thf('113', plain,
% 22.62/22.81      (![X0 : $i, X1 : $i]:
% 22.62/22.81         ((r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 22.62/22.81          | ~ (v3_ordinal1 @ X1)
% 22.62/22.81          | (r2_hidden @ X1 @ X0)
% 22.62/22.81          | ~ (v3_ordinal1 @ X0)
% 22.62/22.81          | ~ (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 22.62/22.81      inference('sup-', [status(thm)], ['111', '112'])).
% 22.62/22.81  thf('114', plain,
% 22.62/22.81      ((~ (v3_ordinal1 @ sk_A)
% 22.62/22.81        | (r2_hidden @ sk_B @ sk_A)
% 22.62/22.81        | ~ (v3_ordinal1 @ sk_B)
% 22.62/22.81        | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 22.62/22.81      inference('sup-', [status(thm)], ['103', '113'])).
% 22.62/22.81  thf('115', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('116', plain, ((v3_ordinal1 @ sk_B)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('117', plain,
% 22.62/22.81      (((r2_hidden @ sk_B @ sk_A) | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 22.62/22.81      inference('demod', [status(thm)], ['114', '115', '116'])).
% 22.62/22.81  thf('118', plain,
% 22.62/22.81      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 22.62/22.81         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 22.62/22.81      inference('split', [status(esa)], ['22'])).
% 22.62/22.81  thf('119', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 22.62/22.81      inference('sat_resolution*', [status(thm)], ['23', '100'])).
% 22.62/22.81  thf('120', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 22.62/22.81      inference('simpl_trail', [status(thm)], ['118', '119'])).
% 22.62/22.81  thf('121', plain, ((r2_hidden @ sk_B @ sk_A)),
% 22.62/22.81      inference('clc', [status(thm)], ['117', '120'])).
% 22.62/22.81  thf('122', plain,
% 22.62/22.81      (![X51 : $i, X52 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 22.62/22.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 22.62/22.81  thf('123', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 22.62/22.81      inference('sup-', [status(thm)], ['121', '122'])).
% 22.62/22.81  thf('124', plain,
% 22.62/22.81      (![X0 : $i]:
% 22.62/22.81         ((r1_tarski @ X0 @ sk_A)
% 22.62/22.81          | (r1_ordinal1 @ sk_A @ X0)
% 22.62/22.81          | ~ (v3_ordinal1 @ X0))),
% 22.62/22.81      inference('simplify', [status(thm)], ['78'])).
% 22.62/22.81  thf('125', plain,
% 22.62/22.81      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('split', [status(esa)], ['3'])).
% 22.62/22.81  thf('126', plain,
% 22.62/22.81      (![X51 : $i, X52 : $i]:
% 22.62/22.81         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 22.62/22.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 22.62/22.81  thf('127', plain,
% 22.62/22.81      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['125', '126'])).
% 22.62/22.81  thf('128', plain,
% 22.62/22.81      (((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B)))
% 22.62/22.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['124', '127'])).
% 22.62/22.81  thf('129', plain, ((v3_ordinal1 @ sk_B)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('130', plain,
% 22.62/22.81      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['128', '129'])).
% 22.62/22.81  thf('131', plain,
% 22.62/22.81      (![X45 : $i, X46 : $i]:
% 22.62/22.81         (~ (v3_ordinal1 @ X45)
% 22.62/22.81          | ~ (v3_ordinal1 @ X46)
% 22.62/22.81          | (r1_tarski @ X45 @ X46)
% 22.62/22.81          | ~ (r1_ordinal1 @ X45 @ X46))),
% 22.62/22.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 22.62/22.81  thf('132', plain,
% 22.62/22.81      ((((r1_tarski @ sk_A @ sk_B)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_B)
% 22.62/22.81         | ~ (v3_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('sup-', [status(thm)], ['130', '131'])).
% 22.62/22.81  thf('133', plain, ((v3_ordinal1 @ sk_B)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('134', plain, ((v3_ordinal1 @ sk_A)),
% 22.62/22.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.62/22.81  thf('135', plain,
% 22.62/22.81      (((r1_tarski @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 22.62/22.81      inference('demod', [status(thm)], ['132', '133', '134'])).
% 22.62/22.81  thf('136', plain, (((r2_hidden @ sk_A @ sk_B))),
% 22.62/22.81      inference('sat_resolution*', [status(thm)], ['23', '100', '101'])).
% 22.62/22.81  thf('137', plain, ((r1_tarski @ sk_A @ sk_B)),
% 22.62/22.81      inference('simpl_trail', [status(thm)], ['135', '136'])).
% 22.62/22.81  thf('138', plain, ($false), inference('demod', [status(thm)], ['123', '137'])).
% 22.62/22.81  
% 22.62/22.81  % SZS output end Refutation
% 22.62/22.81  
% 22.62/22.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
