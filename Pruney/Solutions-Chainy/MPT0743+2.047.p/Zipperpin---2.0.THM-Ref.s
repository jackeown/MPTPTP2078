%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RT10xb7xAN

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:59 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 539 expanded)
%              Number of leaves         :   22 ( 157 expanded)
%              Depth                    :   23
%              Number of atoms          :  991 (4484 expanded)
%              Number of equality atoms :   29 (  81 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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

thf('0',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('3',plain,(
    ! [X49: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X49 ) )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('4',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('14',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ( r1_ordinal1 @ X48 @ X47 )
      | ( r2_hidden @ X47 @ X48 )
      | ~ ( v3_ordinal1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('23',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_ordinal1 @ X45 )
      | ( r2_hidden @ X46 @ X45 )
      | ( X46 = X45 )
      | ( r2_hidden @ X45 @ X46 )
      | ~ ( v3_ordinal1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B )
        | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','36'])).

thf('38',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('42',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('43',plain,(
    ! [X44: $i] :
      ( r2_hidden @ X44 @ ( k1_ordinal1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('44',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','46'])).

thf('48',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf('49',plain,(
    ! [X49: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X49 ) )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('50',plain,(
    ! [X49: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X49 ) )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('51',plain,(
    ! [X49: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X49 ) )
      | ~ ( v3_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v3_ordinal1 @ X39 )
      | ~ ( v3_ordinal1 @ X40 )
      | ( r1_ordinal1 @ X39 @ X40 )
      | ( r1_ordinal1 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('53',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('61',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('68',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( ( k1_ordinal1 @ sk_A )
        = sk_B )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','70'])).

thf('72',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( ( k1_ordinal1 @ sk_A )
        = sk_B ) )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','46'])).

thf('75',plain,
    ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('77',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('78',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('82',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('84',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('85',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('87',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','46','86'])).

thf('88',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('89',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('91',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v3_ordinal1 @ X39 )
      | ~ ( v3_ordinal1 @ X40 )
      | ( r1_ordinal1 @ X39 @ X40 )
      | ( r1_ordinal1 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('106',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('107',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','46','86'])).

thf('109',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['91','112'])).

thf('114',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v3_ordinal1 @ X39 )
      | ~ ( v3_ordinal1 @ X40 )
      | ( r1_ordinal1 @ X39 @ X40 )
      | ( r1_ordinal1 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_B ) ),
    inference(eq_fact,[status(thm)],['116'])).

thf('118',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    r1_ordinal1 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['48','113','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RT10xb7xAN
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.14  % Solved by: fo/fo7.sh
% 0.89/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.14  % done 1463 iterations in 0.688s
% 0.89/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.14  % SZS output start Refutation
% 0.89/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.14  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.89/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.89/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.89/1.14  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.89/1.14  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.89/1.14  thf(t33_ordinal1, conjecture,
% 0.89/1.14    (![A:$i]:
% 0.89/1.14     ( ( v3_ordinal1 @ A ) =>
% 0.89/1.14       ( ![B:$i]:
% 0.89/1.14         ( ( v3_ordinal1 @ B ) =>
% 0.89/1.14           ( ( r2_hidden @ A @ B ) <=>
% 0.89/1.14             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.89/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.14    (~( ![A:$i]:
% 0.89/1.14        ( ( v3_ordinal1 @ A ) =>
% 0.89/1.14          ( ![B:$i]:
% 0.89/1.14            ( ( v3_ordinal1 @ B ) =>
% 0.89/1.14              ( ( r2_hidden @ A @ B ) <=>
% 0.89/1.14                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.89/1.14    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.89/1.14  thf('0', plain,
% 0.89/1.14      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.89/1.14        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('1', plain,
% 0.89/1.14      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('split', [status(esa)], ['0'])).
% 0.89/1.14  thf('2', plain,
% 0.89/1.14      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.89/1.14       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.89/1.14      inference('split', [status(esa)], ['0'])).
% 0.89/1.14  thf(t29_ordinal1, axiom,
% 0.89/1.14    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.89/1.14  thf('3', plain,
% 0.89/1.14      (![X49 : $i]:
% 0.89/1.14         ((v3_ordinal1 @ (k1_ordinal1 @ X49)) | ~ (v3_ordinal1 @ X49))),
% 0.89/1.14      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.89/1.14  thf('4', plain,
% 0.89/1.14      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('5', plain,
% 0.89/1.14      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.89/1.14         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('split', [status(esa)], ['4'])).
% 0.89/1.14  thf(redefinition_r1_ordinal1, axiom,
% 0.89/1.14    (![A:$i,B:$i]:
% 0.89/1.14     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.89/1.14       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.89/1.14  thf('6', plain,
% 0.89/1.14      (![X42 : $i, X43 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X42)
% 0.89/1.14          | ~ (v3_ordinal1 @ X43)
% 0.89/1.14          | (r1_tarski @ X42 @ X43)
% 0.89/1.14          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.89/1.14      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.89/1.14  thf('7', plain,
% 0.89/1.14      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.89/1.14         | ~ (v3_ordinal1 @ sk_B)
% 0.89/1.14         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.14  thf('8', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('9', plain,
% 0.89/1.14      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.89/1.14         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.14  thf('10', plain,
% 0.89/1.14      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.89/1.14         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['3', '9'])).
% 0.89/1.14  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('12', plain,
% 0.89/1.14      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.89/1.14         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['10', '11'])).
% 0.89/1.14  thf(t69_enumset1, axiom,
% 0.89/1.14    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.89/1.14  thf('13', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.89/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.89/1.14  thf(d1_ordinal1, axiom,
% 0.89/1.14    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.89/1.14  thf('14', plain,
% 0.89/1.14      (![X41 : $i]:
% 0.89/1.14         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 0.89/1.14      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.89/1.14  thf('15', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.89/1.14      inference('sup+', [status(thm)], ['13', '14'])).
% 0.89/1.14  thf(t26_ordinal1, axiom,
% 0.89/1.14    (![A:$i]:
% 0.89/1.14     ( ( v3_ordinal1 @ A ) =>
% 0.89/1.14       ( ![B:$i]:
% 0.89/1.14         ( ( v3_ordinal1 @ B ) =>
% 0.89/1.14           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.89/1.14  thf('16', plain,
% 0.89/1.14      (![X47 : $i, X48 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X47)
% 0.89/1.14          | (r1_ordinal1 @ X48 @ X47)
% 0.89/1.14          | (r2_hidden @ X47 @ X48)
% 0.89/1.14          | ~ (v3_ordinal1 @ X48))),
% 0.89/1.14      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.89/1.14  thf('17', plain,
% 0.89/1.14      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('split', [status(esa)], ['0'])).
% 0.89/1.14  thf('18', plain,
% 0.89/1.14      (((~ (v3_ordinal1 @ sk_B)
% 0.89/1.14         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.89/1.14         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['16', '17'])).
% 0.89/1.14  thf('19', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('21', plain,
% 0.89/1.14      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.89/1.14  thf('22', plain,
% 0.89/1.14      (![X42 : $i, X43 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X42)
% 0.89/1.14          | ~ (v3_ordinal1 @ X43)
% 0.89/1.14          | (r1_tarski @ X42 @ X43)
% 0.89/1.14          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.89/1.14      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.89/1.14  thf('23', plain,
% 0.89/1.14      ((((r1_tarski @ sk_B @ sk_A)
% 0.89/1.14         | ~ (v3_ordinal1 @ sk_A)
% 0.89/1.14         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['21', '22'])).
% 0.89/1.14  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('25', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('26', plain,
% 0.89/1.14      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.89/1.14  thf(t24_ordinal1, axiom,
% 0.89/1.14    (![A:$i]:
% 0.89/1.14     ( ( v3_ordinal1 @ A ) =>
% 0.89/1.14       ( ![B:$i]:
% 0.89/1.14         ( ( v3_ordinal1 @ B ) =>
% 0.89/1.14           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.89/1.14                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.89/1.14  thf('27', plain,
% 0.89/1.14      (![X45 : $i, X46 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X45)
% 0.89/1.14          | (r2_hidden @ X46 @ X45)
% 0.89/1.14          | ((X46) = (X45))
% 0.89/1.14          | (r2_hidden @ X45 @ X46)
% 0.89/1.14          | ~ (v3_ordinal1 @ X46))),
% 0.89/1.14      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.89/1.14  thf(t7_ordinal1, axiom,
% 0.89/1.14    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.14  thf('28', plain,
% 0.89/1.14      (![X50 : $i, X51 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X50 @ X51) | ~ (r1_tarski @ X51 @ X50))),
% 0.89/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.89/1.14  thf('29', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X1)
% 0.89/1.14          | (r2_hidden @ X0 @ X1)
% 0.89/1.14          | ((X1) = (X0))
% 0.89/1.14          | ~ (v3_ordinal1 @ X0)
% 0.89/1.14          | ~ (r1_tarski @ X0 @ X1))),
% 0.89/1.14      inference('sup-', [status(thm)], ['27', '28'])).
% 0.89/1.14  thf('30', plain,
% 0.89/1.14      (((~ (v3_ordinal1 @ sk_B)
% 0.89/1.14         | ((sk_A) = (sk_B))
% 0.89/1.14         | (r2_hidden @ sk_B @ sk_A)
% 0.89/1.14         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['26', '29'])).
% 0.89/1.14  thf('31', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('33', plain,
% 0.89/1.14      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_A)))
% 0.89/1.14         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.89/1.14  thf(d3_xboole_0, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.89/1.14       ( ![D:$i]:
% 0.89/1.14         ( ( r2_hidden @ D @ C ) <=>
% 0.89/1.14           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.89/1.14  thf('34', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X0 @ X3)
% 0.89/1.14          | (r2_hidden @ X0 @ X2)
% 0.89/1.14          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.89/1.14      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.89/1.14  thf('35', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.89/1.14         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.89/1.14      inference('simplify', [status(thm)], ['34'])).
% 0.89/1.14  thf('36', plain,
% 0.89/1.14      ((![X0 : $i]:
% 0.89/1.14          (((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_A @ X0))))
% 0.89/1.14         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['33', '35'])).
% 0.89/1.14  thf('37', plain,
% 0.89/1.14      ((((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A)) | ((sk_A) = (sk_B))))
% 0.89/1.14         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('sup+', [status(thm)], ['15', '36'])).
% 0.89/1.14  thf('38', plain,
% 0.89/1.14      (![X50 : $i, X51 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X50 @ X51) | ~ (r1_tarski @ X51 @ X50))),
% 0.89/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.89/1.14  thf('39', plain,
% 0.89/1.14      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.89/1.14         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['37', '38'])).
% 0.89/1.14  thf('40', plain,
% 0.89/1.14      ((((sk_A) = (sk_B)))
% 0.89/1.14         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.89/1.14             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['12', '39'])).
% 0.89/1.14  thf('41', plain,
% 0.89/1.14      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.89/1.14         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['10', '11'])).
% 0.89/1.14  thf('42', plain,
% 0.89/1.14      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.89/1.14         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.89/1.14             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup+', [status(thm)], ['40', '41'])).
% 0.89/1.14  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.89/1.14  thf('43', plain, (![X44 : $i]: (r2_hidden @ X44 @ (k1_ordinal1 @ X44))),
% 0.89/1.14      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.89/1.14  thf('44', plain,
% 0.89/1.14      (![X50 : $i, X51 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X50 @ X51) | ~ (r1_tarski @ X51 @ X50))),
% 0.89/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.89/1.14  thf('45', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.89/1.14      inference('sup-', [status(thm)], ['43', '44'])).
% 0.89/1.14  thf('46', plain,
% 0.89/1.14      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.89/1.14       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.89/1.14      inference('sup-', [status(thm)], ['42', '45'])).
% 0.89/1.14  thf('47', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.89/1.14      inference('sat_resolution*', [status(thm)], ['2', '46'])).
% 0.89/1.14  thf('48', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.89/1.14      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 0.89/1.14  thf('49', plain,
% 0.89/1.14      (![X49 : $i]:
% 0.89/1.14         ((v3_ordinal1 @ (k1_ordinal1 @ X49)) | ~ (v3_ordinal1 @ X49))),
% 0.89/1.14      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.89/1.14  thf('50', plain,
% 0.89/1.14      (![X49 : $i]:
% 0.89/1.14         ((v3_ordinal1 @ (k1_ordinal1 @ X49)) | ~ (v3_ordinal1 @ X49))),
% 0.89/1.14      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.89/1.14  thf('51', plain,
% 0.89/1.14      (![X49 : $i]:
% 0.89/1.14         ((v3_ordinal1 @ (k1_ordinal1 @ X49)) | ~ (v3_ordinal1 @ X49))),
% 0.89/1.14      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.89/1.14  thf(connectedness_r1_ordinal1, axiom,
% 0.89/1.14    (![A:$i,B:$i]:
% 0.89/1.14     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.89/1.14       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.89/1.14  thf('52', plain,
% 0.89/1.14      (![X39 : $i, X40 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X39)
% 0.89/1.14          | ~ (v3_ordinal1 @ X40)
% 0.89/1.14          | (r1_ordinal1 @ X39 @ X40)
% 0.89/1.14          | (r1_ordinal1 @ X40 @ X39))),
% 0.89/1.14      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.89/1.14  thf('53', plain,
% 0.89/1.14      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('split', [status(esa)], ['0'])).
% 0.89/1.14  thf('54', plain,
% 0.89/1.14      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ~ (v3_ordinal1 @ sk_B)
% 0.89/1.14         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['52', '53'])).
% 0.89/1.14  thf('55', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('56', plain,
% 0.89/1.14      ((((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['54', '55'])).
% 0.89/1.14  thf('57', plain,
% 0.89/1.14      (((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['51', '56'])).
% 0.89/1.14  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('59', plain,
% 0.89/1.14      (((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['57', '58'])).
% 0.89/1.14  thf('60', plain,
% 0.89/1.14      (![X42 : $i, X43 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X42)
% 0.89/1.14          | ~ (v3_ordinal1 @ X43)
% 0.89/1.14          | (r1_tarski @ X42 @ X43)
% 0.89/1.14          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.89/1.14      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.89/1.14  thf('61', plain,
% 0.89/1.14      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ~ (v3_ordinal1 @ sk_B)))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['59', '60'])).
% 0.89/1.14  thf('62', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('63', plain,
% 0.89/1.14      ((((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['61', '62'])).
% 0.89/1.14  thf('64', plain,
% 0.89/1.14      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['50', '63'])).
% 0.89/1.14  thf('65', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('66', plain,
% 0.89/1.14      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['64', '65'])).
% 0.89/1.14  thf('67', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X1)
% 0.89/1.14          | (r2_hidden @ X0 @ X1)
% 0.89/1.14          | ((X1) = (X0))
% 0.89/1.14          | ~ (v3_ordinal1 @ X0)
% 0.89/1.14          | ~ (r1_tarski @ X0 @ X1))),
% 0.89/1.14      inference('sup-', [status(thm)], ['27', '28'])).
% 0.89/1.14  thf('68', plain,
% 0.89/1.14      (((~ (v3_ordinal1 @ sk_B)
% 0.89/1.14         | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.89/1.14         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['66', '67'])).
% 0.89/1.14  thf('69', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('70', plain,
% 0.89/1.14      (((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.89/1.14         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['68', '69'])).
% 0.89/1.14  thf('71', plain,
% 0.89/1.14      (((~ (v3_ordinal1 @ sk_A)
% 0.89/1.14         | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ((k1_ordinal1 @ sk_A) = (sk_B))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['49', '70'])).
% 0.89/1.14  thf('72', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('73', plain,
% 0.89/1.14      ((((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14         | ((k1_ordinal1 @ sk_A) = (sk_B))))
% 0.89/1.14         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['71', '72'])).
% 0.89/1.14  thf('74', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.89/1.14      inference('sat_resolution*', [status(thm)], ['2', '46'])).
% 0.89/1.14  thf('75', plain,
% 0.89/1.14      (((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.89/1.14        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.89/1.14      inference('simpl_trail', [status(thm)], ['73', '74'])).
% 0.89/1.14  thf('76', plain,
% 0.89/1.14      (![X41 : $i]:
% 0.89/1.14         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 0.89/1.14      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.89/1.14  thf('77', plain,
% 0.89/1.14      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X4 @ X2)
% 0.89/1.14          | (r2_hidden @ X4 @ X3)
% 0.89/1.14          | (r2_hidden @ X4 @ X1)
% 0.89/1.14          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.89/1.14      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.89/1.14  thf('78', plain,
% 0.89/1.14      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.89/1.14         ((r2_hidden @ X4 @ X1)
% 0.89/1.14          | (r2_hidden @ X4 @ X3)
% 0.89/1.14          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.89/1.14      inference('simplify', [status(thm)], ['77'])).
% 0.89/1.14  thf('79', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.89/1.14          | (r2_hidden @ X1 @ X0)
% 0.89/1.14          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['76', '78'])).
% 0.89/1.14  thf('80', plain,
% 0.89/1.14      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.89/1.14        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.89/1.14        | (r2_hidden @ sk_B @ sk_A))),
% 0.89/1.14      inference('sup-', [status(thm)], ['75', '79'])).
% 0.89/1.14  thf('81', plain,
% 0.89/1.14      (![X50 : $i, X51 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X50 @ X51) | ~ (r1_tarski @ X51 @ X50))),
% 0.89/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.89/1.14  thf('82', plain,
% 0.89/1.14      (((r2_hidden @ sk_B @ sk_A)
% 0.89/1.14        | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.89/1.14        | ~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 0.89/1.14      inference('sup-', [status(thm)], ['80', '81'])).
% 0.89/1.14  thf('83', plain,
% 0.89/1.14      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('split', [status(esa)], ['4'])).
% 0.89/1.14  thf(l1_zfmisc_1, axiom,
% 0.89/1.14    (![A:$i,B:$i]:
% 0.89/1.14     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.89/1.14  thf('84', plain,
% 0.89/1.14      (![X34 : $i, X36 : $i]:
% 0.89/1.14         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.89/1.14      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.89/1.14  thf('85', plain,
% 0.89/1.14      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.89/1.14         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['83', '84'])).
% 0.89/1.14  thf('86', plain,
% 0.89/1.14      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.89/1.14       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.89/1.14      inference('split', [status(esa)], ['4'])).
% 0.89/1.14  thf('87', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.89/1.14      inference('sat_resolution*', [status(thm)], ['2', '46', '86'])).
% 0.89/1.14  thf('88', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.89/1.14      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 0.89/1.14  thf('89', plain,
% 0.89/1.14      (((r2_hidden @ sk_B @ sk_A) | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.89/1.14      inference('demod', [status(thm)], ['82', '88'])).
% 0.89/1.14  thf('90', plain,
% 0.89/1.14      (![X50 : $i, X51 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X50 @ X51) | ~ (r1_tarski @ X51 @ X50))),
% 0.89/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.89/1.14  thf('91', plain,
% 0.89/1.14      ((((k1_ordinal1 @ sk_A) = (sk_B)) | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.89/1.14      inference('sup-', [status(thm)], ['89', '90'])).
% 0.89/1.14  thf('92', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('93', plain,
% 0.89/1.14      (![X39 : $i, X40 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X39)
% 0.89/1.14          | ~ (v3_ordinal1 @ X40)
% 0.89/1.14          | (r1_ordinal1 @ X39 @ X40)
% 0.89/1.14          | (r1_ordinal1 @ X40 @ X39))),
% 0.89/1.14      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.89/1.14  thf('94', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         ((r1_ordinal1 @ X0 @ sk_A)
% 0.89/1.14          | (r1_ordinal1 @ sk_A @ X0)
% 0.89/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['92', '93'])).
% 0.89/1.14  thf('95', plain,
% 0.89/1.14      (![X42 : $i, X43 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X42)
% 0.89/1.14          | ~ (v3_ordinal1 @ X43)
% 0.89/1.14          | (r1_tarski @ X42 @ X43)
% 0.89/1.14          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.89/1.14      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.89/1.14  thf('96', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X0)
% 0.89/1.14          | (r1_ordinal1 @ sk_A @ X0)
% 0.89/1.14          | (r1_tarski @ X0 @ sk_A)
% 0.89/1.14          | ~ (v3_ordinal1 @ sk_A)
% 0.89/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['94', '95'])).
% 0.89/1.14  thf('97', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('98', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X0)
% 0.89/1.14          | (r1_ordinal1 @ sk_A @ X0)
% 0.89/1.14          | (r1_tarski @ X0 @ sk_A)
% 0.89/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.89/1.14      inference('demod', [status(thm)], ['96', '97'])).
% 0.89/1.14  thf('99', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         ((r1_tarski @ X0 @ sk_A)
% 0.89/1.14          | (r1_ordinal1 @ sk_A @ X0)
% 0.89/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.89/1.14      inference('simplify', [status(thm)], ['98'])).
% 0.89/1.14  thf('100', plain,
% 0.89/1.14      (![X42 : $i, X43 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X42)
% 0.89/1.14          | ~ (v3_ordinal1 @ X43)
% 0.89/1.14          | (r1_tarski @ X42 @ X43)
% 0.89/1.14          | ~ (r1_ordinal1 @ X42 @ X43))),
% 0.89/1.14      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.89/1.14  thf('101', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X0)
% 0.89/1.14          | (r1_tarski @ X0 @ sk_A)
% 0.89/1.14          | (r1_tarski @ sk_A @ X0)
% 0.89/1.14          | ~ (v3_ordinal1 @ X0)
% 0.89/1.14          | ~ (v3_ordinal1 @ sk_A))),
% 0.89/1.14      inference('sup-', [status(thm)], ['99', '100'])).
% 0.89/1.14  thf('102', plain, ((v3_ordinal1 @ sk_A)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('103', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X0)
% 0.89/1.14          | (r1_tarski @ X0 @ sk_A)
% 0.89/1.14          | (r1_tarski @ sk_A @ X0)
% 0.89/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.89/1.14      inference('demod', [status(thm)], ['101', '102'])).
% 0.89/1.14  thf('104', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         ((r1_tarski @ sk_A @ X0)
% 0.89/1.14          | (r1_tarski @ X0 @ sk_A)
% 0.89/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.89/1.14      inference('simplify', [status(thm)], ['103'])).
% 0.89/1.14  thf('105', plain,
% 0.89/1.14      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('split', [status(esa)], ['4'])).
% 0.89/1.14  thf('106', plain,
% 0.89/1.14      (![X50 : $i, X51 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X50 @ X51) | ~ (r1_tarski @ X51 @ X50))),
% 0.89/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.89/1.14  thf('107', plain,
% 0.89/1.14      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['105', '106'])).
% 0.89/1.14  thf('108', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.89/1.14      inference('sat_resolution*', [status(thm)], ['2', '46', '86'])).
% 0.89/1.14  thf('109', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.89/1.14      inference('simpl_trail', [status(thm)], ['107', '108'])).
% 0.89/1.14  thf('110', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.89/1.14      inference('sup-', [status(thm)], ['104', '109'])).
% 0.89/1.14  thf('111', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('112', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.89/1.14      inference('demod', [status(thm)], ['110', '111'])).
% 0.89/1.14  thf('113', plain, (((k1_ordinal1 @ sk_A) = (sk_B))),
% 0.89/1.14      inference('demod', [status(thm)], ['91', '112'])).
% 0.89/1.14  thf('114', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('115', plain,
% 0.89/1.14      (![X39 : $i, X40 : $i]:
% 0.89/1.14         (~ (v3_ordinal1 @ X39)
% 0.89/1.14          | ~ (v3_ordinal1 @ X40)
% 0.89/1.14          | (r1_ordinal1 @ X39 @ X40)
% 0.89/1.14          | (r1_ordinal1 @ X40 @ X39))),
% 0.89/1.14      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.89/1.14  thf('116', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         ((r1_ordinal1 @ X0 @ sk_B)
% 0.89/1.14          | (r1_ordinal1 @ sk_B @ X0)
% 0.89/1.14          | ~ (v3_ordinal1 @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['114', '115'])).
% 0.89/1.14  thf('117', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_B @ sk_B))),
% 0.89/1.14      inference('eq_fact', [status(thm)], ['116'])).
% 0.89/1.14  thf('118', plain, ((v3_ordinal1 @ sk_B)),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('119', plain, ((r1_ordinal1 @ sk_B @ sk_B)),
% 0.89/1.14      inference('demod', [status(thm)], ['117', '118'])).
% 0.89/1.14  thf('120', plain, ($false),
% 0.89/1.14      inference('demod', [status(thm)], ['48', '113', '119'])).
% 0.89/1.14  
% 0.89/1.14  % SZS output end Refutation
% 0.89/1.14  
% 0.89/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
