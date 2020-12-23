%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2m547WSLnr

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:32 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 251 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   23
%              Number of atoms          :  854 (2796 expanded)
%              Number of equality atoms :  150 ( 595 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( X26 = X23 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r2_hidden @ X46 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','19'])).

thf('21',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = sk_C_1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('28',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39
        = ( k1_tarski @ X38 ) )
      | ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ X39 @ ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('31',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('34',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ ( k1_tarski @ X40 ) )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('35',plain,(
    ! [X40: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( ( k2_xboole_0 @ sk_B_1 @ X0 )
          = X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( ( k2_xboole_0 @ sk_B_1 @ X0 )
          = X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = sk_C_1 )
      | ( sk_C_1 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','45'])).

thf('47',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('50',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('53',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('54',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['49','51','55'])).

thf('57',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['48','56'])).

thf('58',plain,
    ( ( sk_C_1 = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','57'])).

thf('59',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','64'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('66',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 != X43 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('67',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('68',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('71',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X43: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,
    ( ( k1_xboole_0 != sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('76',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('79',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','79'])).

thf('81',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['21','80'])).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('83',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference('sup+',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('91',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['0','91'])).

thf('93',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['48','56'])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2m547WSLnr
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.83/2.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.83/2.02  % Solved by: fo/fo7.sh
% 1.83/2.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.83/2.02  % done 2491 iterations in 1.572s
% 1.83/2.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.83/2.02  % SZS output start Refutation
% 1.83/2.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.83/2.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.83/2.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.83/2.02  thf(sk_A_type, type, sk_A: $i).
% 1.83/2.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.83/2.02  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.83/2.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.83/2.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.83/2.02  thf(sk_B_type, type, sk_B: $i > $i).
% 1.83/2.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.83/2.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.83/2.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.83/2.02  thf(t43_zfmisc_1, conjecture,
% 1.83/2.02    (![A:$i,B:$i,C:$i]:
% 1.83/2.02     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.83/2.02          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.83/2.02          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.83/2.02          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.83/2.02  thf(zf_stmt_0, negated_conjecture,
% 1.83/2.02    (~( ![A:$i,B:$i,C:$i]:
% 1.83/2.02        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.83/2.02             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.83/2.02             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.83/2.02             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.83/2.02    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.83/2.02  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.83/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.02  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.83/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.02  thf(t7_xboole_0, axiom,
% 1.83/2.02    (![A:$i]:
% 1.83/2.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.83/2.02          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.83/2.02  thf('2', plain,
% 1.83/2.02      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.83/2.02      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.83/2.02  thf(d3_xboole_0, axiom,
% 1.83/2.02    (![A:$i,B:$i,C:$i]:
% 1.83/2.02     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.83/2.02       ( ![D:$i]:
% 1.83/2.02         ( ( r2_hidden @ D @ C ) <=>
% 1.83/2.02           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.83/2.02  thf('3', plain,
% 1.83/2.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.83/2.02         (~ (r2_hidden @ X0 @ X1)
% 1.83/2.02          | (r2_hidden @ X0 @ X2)
% 1.83/2.02          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.83/2.02      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.83/2.02  thf('4', plain,
% 1.83/2.02      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.83/2.02         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.83/2.02      inference('simplify', [status(thm)], ['3'])).
% 1.83/2.02  thf('5', plain,
% 1.83/2.02      (![X0 : $i, X1 : $i]:
% 1.83/2.02         (((X0) = (k1_xboole_0))
% 1.83/2.02          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.83/2.02      inference('sup-', [status(thm)], ['2', '4'])).
% 1.83/2.02  thf('6', plain,
% 1.83/2.02      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 1.83/2.02        | ((sk_C_1) = (k1_xboole_0)))),
% 1.83/2.02      inference('sup+', [status(thm)], ['1', '5'])).
% 1.83/2.02  thf(d1_tarski, axiom,
% 1.83/2.02    (![A:$i,B:$i]:
% 1.83/2.02     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.83/2.02       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.83/2.02  thf('7', plain,
% 1.83/2.02      (![X23 : $i, X25 : $i, X26 : $i]:
% 1.83/2.02         (~ (r2_hidden @ X26 @ X25)
% 1.83/2.02          | ((X26) = (X23))
% 1.83/2.02          | ((X25) != (k1_tarski @ X23)))),
% 1.83/2.02      inference('cnf', [status(esa)], [d1_tarski])).
% 1.83/2.02  thf('8', plain,
% 1.83/2.02      (![X23 : $i, X26 : $i]:
% 1.83/2.02         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 1.83/2.02      inference('simplify', [status(thm)], ['7'])).
% 1.83/2.02  thf('9', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 1.83/2.02      inference('sup-', [status(thm)], ['6', '8'])).
% 1.83/2.02  thf('10', plain,
% 1.83/2.02      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.83/2.02      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.83/2.02  thf('11', plain,
% 1.83/2.02      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.83/2.02      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.83/2.02  thf(t38_zfmisc_1, axiom,
% 1.83/2.02    (![A:$i,B:$i,C:$i]:
% 1.83/2.02     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.83/2.02       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.83/2.02  thf('12', plain,
% 1.83/2.02      (![X46 : $i, X48 : $i, X49 : $i]:
% 1.83/2.02         ((r1_tarski @ (k2_tarski @ X46 @ X48) @ X49)
% 1.83/2.02          | ~ (r2_hidden @ X48 @ X49)
% 1.83/2.02          | ~ (r2_hidden @ X46 @ X49))),
% 1.83/2.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.83/2.02  thf('13', plain,
% 1.83/2.02      (![X0 : $i, X1 : $i]:
% 1.83/2.02         (((X0) = (k1_xboole_0))
% 1.83/2.02          | ~ (r2_hidden @ X1 @ X0)
% 1.83/2.02          | (r1_tarski @ (k2_tarski @ X1 @ (sk_B @ X0)) @ X0))),
% 1.83/2.02      inference('sup-', [status(thm)], ['11', '12'])).
% 1.83/2.02  thf('14', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         (((X0) = (k1_xboole_0))
% 1.83/2.02          | (r1_tarski @ (k2_tarski @ (sk_B @ X0) @ (sk_B @ X0)) @ X0)
% 1.83/2.02          | ((X0) = (k1_xboole_0)))),
% 1.83/2.02      inference('sup-', [status(thm)], ['10', '13'])).
% 1.83/2.02  thf(t69_enumset1, axiom,
% 1.83/2.02    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.83/2.02  thf('15', plain,
% 1.83/2.02      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 1.83/2.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.83/2.02  thf('16', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         (((X0) = (k1_xboole_0))
% 1.83/2.02          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 1.83/2.02          | ((X0) = (k1_xboole_0)))),
% 1.83/2.02      inference('demod', [status(thm)], ['14', '15'])).
% 1.83/2.02  thf('17', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         ((r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0) | ((X0) = (k1_xboole_0)))),
% 1.83/2.02      inference('simplify', [status(thm)], ['16'])).
% 1.83/2.02  thf(t12_xboole_1, axiom,
% 1.83/2.02    (![A:$i,B:$i]:
% 1.83/2.02     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.83/2.02  thf('18', plain,
% 1.83/2.02      (![X15 : $i, X16 : $i]:
% 1.83/2.02         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.83/2.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.83/2.02  thf('19', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         (((X0) = (k1_xboole_0))
% 1.83/2.02          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 1.83/2.02      inference('sup-', [status(thm)], ['17', '18'])).
% 1.83/2.02  thf('20', plain,
% 1.83/2.02      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))
% 1.83/2.02        | ((sk_C_1) = (k1_xboole_0))
% 1.83/2.02        | ((sk_C_1) = (k1_xboole_0)))),
% 1.83/2.02      inference('sup+', [status(thm)], ['9', '19'])).
% 1.83/2.02  thf('21', plain,
% 1.83/2.02      ((((sk_C_1) = (k1_xboole_0))
% 1.83/2.02        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1)))),
% 1.83/2.02      inference('simplify', [status(thm)], ['20'])).
% 1.83/2.02  thf('22', plain,
% 1.83/2.02      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.83/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.02  thf('23', plain,
% 1.83/2.02      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.83/2.02      inference('split', [status(esa)], ['22'])).
% 1.83/2.02  thf('24', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.83/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.02  thf('25', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.83/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.02  thf(t7_xboole_1, axiom,
% 1.83/2.02    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.83/2.02  thf('26', plain,
% 1.83/2.02      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 1.83/2.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.83/2.02  thf('27', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.83/2.02      inference('sup+', [status(thm)], ['25', '26'])).
% 1.83/2.02  thf(l3_zfmisc_1, axiom,
% 1.83/2.02    (![A:$i,B:$i]:
% 1.83/2.02     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.83/2.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.83/2.02  thf('28', plain,
% 1.83/2.02      (![X38 : $i, X39 : $i]:
% 1.83/2.02         (((X39) = (k1_tarski @ X38))
% 1.83/2.02          | ((X39) = (k1_xboole_0))
% 1.83/2.02          | ~ (r1_tarski @ X39 @ (k1_tarski @ X38)))),
% 1.83/2.02      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.83/2.02  thf('29', plain,
% 1.83/2.02      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.83/2.02      inference('sup-', [status(thm)], ['27', '28'])).
% 1.83/2.02  thf('30', plain,
% 1.83/2.02      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.83/2.02         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('split', [status(esa)], ['22'])).
% 1.83/2.02  thf('31', plain,
% 1.83/2.02      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 1.83/2.02         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('sup-', [status(thm)], ['29', '30'])).
% 1.83/2.02  thf('32', plain,
% 1.83/2.02      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('simplify', [status(thm)], ['31'])).
% 1.83/2.02  thf('33', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         ((r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0) | ((X0) = (k1_xboole_0)))),
% 1.83/2.02      inference('simplify', [status(thm)], ['16'])).
% 1.83/2.02  thf('34', plain,
% 1.83/2.02      (![X39 : $i, X40 : $i]:
% 1.83/2.02         ((r1_tarski @ X39 @ (k1_tarski @ X40)) | ((X39) != (k1_xboole_0)))),
% 1.83/2.02      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.83/2.02  thf('35', plain,
% 1.83/2.02      (![X40 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X40))),
% 1.83/2.02      inference('simplify', [status(thm)], ['34'])).
% 1.83/2.02  thf('36', plain,
% 1.83/2.02      (![X15 : $i, X16 : $i]:
% 1.83/2.02         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.83/2.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.83/2.02  thf('37', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 1.83/2.02      inference('sup-', [status(thm)], ['35', '36'])).
% 1.83/2.02  thf(t11_xboole_1, axiom,
% 1.83/2.02    (![A:$i,B:$i,C:$i]:
% 1.83/2.02     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.83/2.02  thf('38', plain,
% 1.83/2.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.83/2.02         ((r1_tarski @ X12 @ X13)
% 1.83/2.02          | ~ (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ X13))),
% 1.83/2.02      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.83/2.02  thf('39', plain,
% 1.83/2.02      (![X0 : $i, X1 : $i]:
% 1.83/2.02         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.83/2.02          | (r1_tarski @ k1_xboole_0 @ X1))),
% 1.83/2.02      inference('sup-', [status(thm)], ['37', '38'])).
% 1.83/2.02  thf('40', plain,
% 1.83/2.02      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.83/2.02      inference('sup-', [status(thm)], ['33', '39'])).
% 1.83/2.02  thf('41', plain,
% 1.83/2.02      (![X15 : $i, X16 : $i]:
% 1.83/2.02         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.83/2.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.83/2.02  thf('42', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         (((X0) = (k1_xboole_0)) | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 1.83/2.02      inference('sup-', [status(thm)], ['40', '41'])).
% 1.83/2.02  thf('43', plain,
% 1.83/2.02      ((![X0 : $i]:
% 1.83/2.02          (((k2_xboole_0 @ sk_B_1 @ X0) = (X0)) | ((X0) = (k1_xboole_0))))
% 1.83/2.02         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('sup+', [status(thm)], ['32', '42'])).
% 1.83/2.02  thf('44', plain,
% 1.83/2.02      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('simplify', [status(thm)], ['31'])).
% 1.83/2.02  thf('45', plain,
% 1.83/2.02      ((![X0 : $i]: (((k2_xboole_0 @ sk_B_1 @ X0) = (X0)) | ((X0) = (sk_B_1))))
% 1.83/2.02         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('demod', [status(thm)], ['43', '44'])).
% 1.83/2.02  thf('46', plain,
% 1.83/2.02      (((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_C_1) = (sk_B_1))))
% 1.83/2.02         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('sup+', [status(thm)], ['24', '45'])).
% 1.83/2.02  thf('47', plain,
% 1.83/2.02      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.83/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.02  thf('48', plain,
% 1.83/2.02      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.83/2.02         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('split', [status(esa)], ['47'])).
% 1.83/2.02  thf('49', plain,
% 1.83/2.02      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.83/2.02      inference('split', [status(esa)], ['47'])).
% 1.83/2.02  thf('50', plain,
% 1.83/2.02      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.83/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.02  thf('51', plain,
% 1.83/2.02      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 1.83/2.02       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.83/2.02      inference('split', [status(esa)], ['50'])).
% 1.83/2.02  thf('52', plain,
% 1.83/2.02      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('simplify', [status(thm)], ['31'])).
% 1.83/2.02  thf('53', plain,
% 1.83/2.02      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.83/2.02      inference('split', [status(esa)], ['47'])).
% 1.83/2.02  thf('54', plain,
% 1.83/2.02      ((((sk_B_1) != (sk_B_1)))
% 1.83/2.02         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.83/2.02             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('sup-', [status(thm)], ['52', '53'])).
% 1.83/2.02  thf('55', plain,
% 1.83/2.02      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.83/2.02      inference('simplify', [status(thm)], ['54'])).
% 1.83/2.02  thf('56', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.83/2.02      inference('sat_resolution*', [status(thm)], ['49', '51', '55'])).
% 1.83/2.02  thf('57', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.83/2.02      inference('simpl_trail', [status(thm)], ['48', '56'])).
% 1.83/2.02  thf('58', plain,
% 1.83/2.02      ((((sk_C_1) = (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('simplify_reflect-', [status(thm)], ['46', '57'])).
% 1.83/2.02  thf('59', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.83/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.02  thf('60', plain,
% 1.83/2.02      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_B_1)))
% 1.83/2.02         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('sup+', [status(thm)], ['58', '59'])).
% 1.83/2.02  thf(d10_xboole_0, axiom,
% 1.83/2.02    (![A:$i,B:$i]:
% 1.83/2.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.83/2.02  thf('61', plain,
% 1.83/2.02      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.83/2.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.83/2.02  thf('62', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.83/2.02      inference('simplify', [status(thm)], ['61'])).
% 1.83/2.02  thf('63', plain,
% 1.83/2.02      (![X15 : $i, X16 : $i]:
% 1.83/2.02         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.83/2.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.83/2.02  thf('64', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.83/2.02      inference('sup-', [status(thm)], ['62', '63'])).
% 1.83/2.02  thf('65', plain,
% 1.83/2.02      ((((k1_tarski @ sk_A) = (sk_B_1)))
% 1.83/2.02         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('demod', [status(thm)], ['60', '64'])).
% 1.83/2.02  thf(t20_zfmisc_1, axiom,
% 1.83/2.02    (![A:$i,B:$i]:
% 1.83/2.02     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.83/2.02         ( k1_tarski @ A ) ) <=>
% 1.83/2.02       ( ( A ) != ( B ) ) ))).
% 1.83/2.02  thf('66', plain,
% 1.83/2.02      (![X43 : $i, X44 : $i]:
% 1.83/2.02         (((X44) != (X43))
% 1.83/2.02          | ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X43))
% 1.83/2.02              != (k1_tarski @ X44)))),
% 1.83/2.02      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.83/2.02  thf('67', plain,
% 1.83/2.02      (![X43 : $i]:
% 1.83/2.02         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 1.83/2.02           != (k1_tarski @ X43))),
% 1.83/2.02      inference('simplify', [status(thm)], ['66'])).
% 1.83/2.02  thf(t3_boole, axiom,
% 1.83/2.02    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.83/2.02  thf('68', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.83/2.02      inference('cnf', [status(esa)], [t3_boole])).
% 1.83/2.02  thf(t48_xboole_1, axiom,
% 1.83/2.02    (![A:$i,B:$i]:
% 1.83/2.02     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.83/2.02  thf('69', plain,
% 1.83/2.02      (![X19 : $i, X20 : $i]:
% 1.83/2.02         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.83/2.02           = (k3_xboole_0 @ X19 @ X20))),
% 1.83/2.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.83/2.02  thf('70', plain,
% 1.83/2.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.83/2.02      inference('sup+', [status(thm)], ['68', '69'])).
% 1.83/2.02  thf(t2_boole, axiom,
% 1.83/2.02    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.83/2.02  thf('71', plain,
% 1.83/2.02      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 1.83/2.02      inference('cnf', [status(esa)], [t2_boole])).
% 1.83/2.02  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.83/2.02      inference('demod', [status(thm)], ['70', '71'])).
% 1.83/2.02  thf('73', plain, (![X43 : $i]: ((k1_xboole_0) != (k1_tarski @ X43))),
% 1.83/2.02      inference('demod', [status(thm)], ['67', '72'])).
% 1.83/2.02  thf('74', plain,
% 1.83/2.02      ((((k1_xboole_0) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('sup-', [status(thm)], ['65', '73'])).
% 1.83/2.02  thf('75', plain,
% 1.83/2.02      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('simplify', [status(thm)], ['31'])).
% 1.83/2.02  thf('76', plain,
% 1.83/2.02      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.83/2.02      inference('demod', [status(thm)], ['74', '75'])).
% 1.83/2.02  thf('77', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.83/2.02      inference('simplify', [status(thm)], ['76'])).
% 1.83/2.02  thf('78', plain,
% 1.83/2.02      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.83/2.02      inference('split', [status(esa)], ['22'])).
% 1.83/2.02  thf('79', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.83/2.02      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 1.83/2.02  thf('80', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.83/2.02      inference('simpl_trail', [status(thm)], ['23', '79'])).
% 1.83/2.02  thf('81', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))),
% 1.83/2.02      inference('simplify_reflect-', [status(thm)], ['21', '80'])).
% 1.83/2.02  thf('82', plain,
% 1.83/2.02      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 1.83/2.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.83/2.02  thf('83', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.83/2.02      inference('sup+', [status(thm)], ['25', '26'])).
% 1.83/2.02  thf('84', plain,
% 1.83/2.02      (![X15 : $i, X16 : $i]:
% 1.83/2.02         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.83/2.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.83/2.02  thf('85', plain,
% 1.83/2.02      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.83/2.02      inference('sup-', [status(thm)], ['83', '84'])).
% 1.83/2.02  thf('86', plain,
% 1.83/2.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.83/2.02         ((r1_tarski @ X12 @ X13)
% 1.83/2.02          | ~ (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ X13))),
% 1.83/2.02      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.83/2.02  thf('87', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 1.83/2.02      inference('sup-', [status(thm)], ['85', '86'])).
% 1.83/2.02  thf('88', plain,
% 1.83/2.02      (![X0 : $i]:
% 1.83/2.02         (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 1.83/2.02      inference('sup-', [status(thm)], ['82', '87'])).
% 1.83/2.02  thf('89', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 1.83/2.02      inference('sup+', [status(thm)], ['81', '88'])).
% 1.83/2.02  thf('90', plain,
% 1.83/2.02      (![X15 : $i, X16 : $i]:
% 1.83/2.02         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.83/2.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.83/2.02  thf('91', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 1.83/2.02      inference('sup-', [status(thm)], ['89', '90'])).
% 1.83/2.02  thf('92', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 1.83/2.02      inference('sup+', [status(thm)], ['0', '91'])).
% 1.83/2.02  thf('93', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.83/2.02      inference('simpl_trail', [status(thm)], ['48', '56'])).
% 1.83/2.02  thf('94', plain, ($false),
% 1.83/2.02      inference('simplify_reflect-', [status(thm)], ['92', '93'])).
% 1.83/2.02  
% 1.83/2.02  % SZS output end Refutation
% 1.83/2.02  
% 1.83/2.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
