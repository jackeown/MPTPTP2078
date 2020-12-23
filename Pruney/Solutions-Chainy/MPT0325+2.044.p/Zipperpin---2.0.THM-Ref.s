%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zmCXY0swDm

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:46 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 155 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   30
%              Number of atoms          :  670 (1321 expanded)
%              Number of equality atoms :   35 (  65 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X19 ) )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_D )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_C_2 )
      | ( r1_tarski @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_C_2 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['20'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X1 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_B @ X1 )
        | ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_B @ X1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_B @ X1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ X0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','39'])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_zfmisc_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,(
    ! [X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['50','52'])).

thf('54',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['20'])).

thf('56',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['21','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['19','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['4','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_zfmisc_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('71',plain,(
    ! [X22: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','69','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zmCXY0swDm
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 540 iterations in 0.334s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.59/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.80  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.59/0.80  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(t138_zfmisc_1, conjecture,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.59/0.80       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.80         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.59/0.80          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.80            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.59/0.80  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t3_boole, axiom,
% 0.59/0.80    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.80  thf('1', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.80  thf(t83_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      (![X12 : $i, X14 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.80  thf('4', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.59/0.80      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.80  thf(t3_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.59/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf(d3_tarski, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf(l54_zfmisc_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.59/0.80       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.59/0.80         ((r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X19))
% 0.59/0.80          | ~ (r2_hidden @ X17 @ X19)
% 0.59/0.80          | ~ (r2_hidden @ X15 @ X16))),
% 0.59/0.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X0 @ X1)
% 0.59/0.80          | ~ (r2_hidden @ X3 @ X2)
% 0.59/0.80          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.59/0.80             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X0 @ X1)
% 0.59/0.80          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.59/0.80             (k2_zfmisc_1 @ X0 @ X2))
% 0.59/0.80          | (r1_tarski @ X2 @ X3))),
% 0.59/0.80      inference('sup-', [status(thm)], ['6', '9'])).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.80          | (r2_hidden @ X0 @ X2)
% 0.59/0.80          | ~ (r1_tarski @ X1 @ X2))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.59/0.80          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r1_tarski @ sk_A @ X1)
% 0.59/0.80          | (r2_hidden @ 
% 0.59/0.80             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.59/0.80             (k2_zfmisc_1 @ sk_C_2 @ sk_D)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['10', '13'])).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.80         ((r2_hidden @ X17 @ X18)
% 0.59/0.80          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X18)))),
% 0.59/0.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_A @ X1)
% 0.59/0.80          | (r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_D))),
% 0.59/0.80      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B @ sk_D)
% 0.59/0.80          | (r1_tarski @ sk_A @ X0)
% 0.59/0.80          | (r1_tarski @ sk_B @ sk_D))),
% 0.59/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ sk_D))),
% 0.59/0.80      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.59/0.80      inference('split', [status(esa)], ['20'])).
% 0.59/0.80  thf('22', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.59/0.80      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r1_tarski @ sk_A @ X1)
% 0.59/0.80          | (r2_hidden @ 
% 0.59/0.80             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.59/0.80             (k2_zfmisc_1 @ sk_C_2 @ sk_D)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['10', '13'])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.80         ((r2_hidden @ X15 @ X16)
% 0.59/0.80          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X18)))),
% 0.59/0.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_A @ X1)
% 0.59/0.80          | (r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_C_2))),
% 0.59/0.80      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X1 : $i, X3 : $i]:
% 0.59/0.80         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((r1_tarski @ sk_B @ X0)
% 0.59/0.80          | (r1_tarski @ sk_A @ sk_C_2)
% 0.59/0.80          | (r1_tarski @ sk_A @ sk_C_2))),
% 0.59/0.80      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X0 : $i]: ((r1_tarski @ sk_A @ sk_C_2) | (r1_tarski @ sk_B @ X0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['28'])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('split', [status(esa)], ['20'])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 0.59/0.80         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.80          | (r2_hidden @ X0 @ X2)
% 0.59/0.80          | ~ (r1_tarski @ X1 @ X2))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      ((![X0 : $i, X1 : $i]:
% 0.59/0.80          ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_B)))
% 0.59/0.80         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      ((![X0 : $i, X1 : $i]:
% 0.59/0.80          ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X1)))
% 0.59/0.80         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['23', '33'])).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X6 @ X4)
% 0.59/0.80          | ~ (r2_hidden @ X6 @ X7)
% 0.59/0.80          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.59/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.59/0.80          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.59/0.80      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      ((![X0 : $i, X1 : $i]:
% 0.59/0.80          ((r1_xboole_0 @ sk_B @ X1)
% 0.59/0.80           | ~ (r1_xboole_0 @ sk_B @ X0)
% 0.59/0.80           | (r1_xboole_0 @ sk_B @ X1)))
% 0.59/0.80         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['34', '37'])).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      ((![X0 : $i, X1 : $i]:
% 0.59/0.80          (~ (r1_xboole_0 @ sk_B @ X0) | (r1_xboole_0 @ sk_B @ X1)))
% 0.59/0.80         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['38'])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ X0))
% 0.59/0.80         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['22', '39'])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i]:
% 0.59/0.80         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.59/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))
% 0.59/0.80         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.80  thf('43', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.80  thf(t48_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.59/0.80           = (k3_xboole_0 @ X10 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['43', '44'])).
% 0.59/0.80  thf(t2_boole, axiom,
% 0.59/0.80    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_boole])).
% 0.59/0.80  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['45', '46'])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['42', '47'])).
% 0.59/0.80  thf('49', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.80         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.80  thf(t113_zfmisc_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.80       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (![X21 : $i, X22 : $i]:
% 0.59/0.80         (((k2_zfmisc_1 @ X21 @ X22) = (k1_xboole_0))
% 0.59/0.80          | ((X22) != (k1_xboole_0)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.80  thf('52', plain,
% 0.59/0.80      (![X21 : $i]: ((k2_zfmisc_1 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['51'])).
% 0.59/0.80  thf('53', plain,
% 0.59/0.80      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.59/0.80      inference('demod', [status(thm)], ['50', '52'])).
% 0.59/0.80  thf('54', plain, (((r1_tarski @ sk_A @ sk_C_2))),
% 0.59/0.80      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_2))),
% 0.59/0.80      inference('split', [status(esa)], ['20'])).
% 0.59/0.80  thf('56', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 0.59/0.80      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.59/0.80  thf('57', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['21', '56'])).
% 0.59/0.80  thf('58', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.59/0.80      inference('clc', [status(thm)], ['19', '57'])).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.80          | (r2_hidden @ X0 @ X2)
% 0.59/0.80          | ~ (r1_tarski @ X1 @ X2))),
% 0.59/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.80  thf('60', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.80  thf('61', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['5', '60'])).
% 0.59/0.80  thf('62', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.59/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.59/0.80          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.59/0.80      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.80  thf('63', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ sk_A @ X1)
% 0.59/0.80          | ~ (r1_xboole_0 @ sk_A @ X0)
% 0.59/0.80          | (r1_xboole_0 @ sk_A @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['61', '62'])).
% 0.59/0.80  thf('64', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r1_xboole_0 @ sk_A @ X0) | (r1_xboole_0 @ sk_A @ X1))),
% 0.59/0.80      inference('simplify', [status(thm)], ['63'])).
% 0.59/0.80  thf('65', plain, (![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)),
% 0.59/0.80      inference('sup-', [status(thm)], ['4', '64'])).
% 0.59/0.80  thf('66', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i]:
% 0.59/0.80         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.59/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.59/0.80  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.80  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['45', '46'])).
% 0.59/0.80  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['67', '68'])).
% 0.59/0.80  thf('70', plain,
% 0.59/0.80      (![X21 : $i, X22 : $i]:
% 0.59/0.80         (((k2_zfmisc_1 @ X21 @ X22) = (k1_xboole_0))
% 0.59/0.80          | ((X21) != (k1_xboole_0)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.80  thf('71', plain,
% 0.59/0.80      (![X22 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['70'])).
% 0.59/0.80  thf('72', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['0', '69', '71'])).
% 0.59/0.80  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
