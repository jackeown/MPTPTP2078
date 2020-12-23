%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.reaupEzYPL

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:06 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 304 expanded)
%              Number of leaves         :   23 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  740 (3304 expanded)
%              Number of equality atoms :   58 ( 301 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(t34_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
      <=> ( ( A = C )
          & ( B = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_zfmisc_1])).

thf('0',plain,
    ( ( sk_B_1 != sk_D_2 )
    | ( sk_A != sk_C_3 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) )
    | ( sk_B_1 != sk_D_2 )
    | ( sk_A != sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ~ ( r2_hidden @ ( k4_tarski @ X38 @ X40 ) @ ( k2_zfmisc_1 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A = sk_C_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( sk_A != sk_C_3 )
   <= ( sk_A != sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_3 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_C_3 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( sk_A = sk_C_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D_2 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X40 @ X41 )
      | ~ ( r2_hidden @ ( k4_tarski @ X38 @ X40 ) @ ( k2_zfmisc_1 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('19',plain,
    ( ( sk_B_1 = sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B_1 != sk_D_2 )
   <= ( sk_B_1 != sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != sk_D_2 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_1 = sk_D_2 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','12','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( sk_A = sk_C_3 )
   <= ( sk_A = sk_C_3 ) ),
    inference(split,[status(esa)],['3'])).

thf('26',plain,
    ( ( sk_A = sk_C_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,(
    sk_A = sk_C_3 ),
    inference('sat_resolution*',[status(thm)],['2','12','22','26'])).

thf('28',plain,(
    sk_A = sk_C_3 ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_B_1 = sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B_1 = sk_D_2 )
   <= ( sk_B_1 = sk_D_2 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( sk_B_1 = sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ ( k1_tarski @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,(
    sk_B_1 = sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['2','12','22','31'])).

thf('33',plain,(
    sk_B_1 = sk_D_2 ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['24','28','33'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('37',plain,(
    ! [X35: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ X37 )
        = ( k1_tarski @ X35 ) )
      | ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

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

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('52',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ( ( k3_xboole_0 @ X34 @ ( k1_tarski @ X33 ) )
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
       != ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference(clc,[status(thm)],['41','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
       != ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('60',plain,(
    ! [X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X38 @ X40 ) @ ( k2_zfmisc_1 @ X39 @ X42 ) )
      | ~ ( r2_hidden @ X40 @ X42 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['34','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.reaupEzYPL
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.92  % Solved by: fo/fo7.sh
% 0.68/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.92  % done 698 iterations in 0.458s
% 0.68/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.92  % SZS output start Refutation
% 0.68/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.92  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.68/0.92  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.68/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.92  thf(sk_B_type, type, sk_B: $i > $i).
% 0.68/0.92  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.68/0.92  thf(t34_zfmisc_1, conjecture,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.92     ( ( r2_hidden @
% 0.68/0.92         ( k4_tarski @ A @ B ) @ 
% 0.68/0.92         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.68/0.92       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.68/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.92    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.92        ( ( r2_hidden @
% 0.68/0.92            ( k4_tarski @ A @ B ) @ 
% 0.68/0.92            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.68/0.92          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.68/0.92    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.68/0.92  thf('0', plain,
% 0.68/0.92      ((((sk_B_1) != (sk_D_2))
% 0.68/0.92        | ((sk_A) != (sk_C_3))
% 0.68/0.92        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92             (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('1', plain,
% 0.68/0.92      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92           (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))
% 0.68/0.92         <= (~
% 0.68/0.92             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('split', [status(esa)], ['0'])).
% 0.68/0.92  thf('2', plain,
% 0.68/0.92      (~
% 0.68/0.92       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))) | 
% 0.68/0.92       ~ (((sk_B_1) = (sk_D_2))) | ~ (((sk_A) = (sk_C_3)))),
% 0.68/0.92      inference('split', [status(esa)], ['0'])).
% 0.68/0.92  thf('3', plain,
% 0.68/0.92      ((((sk_A) = (sk_C_3))
% 0.68/0.92        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92           (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('4', plain,
% 0.68/0.92      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))
% 0.68/0.92         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('split', [status(esa)], ['3'])).
% 0.68/0.92  thf(l54_zfmisc_1, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.92     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.68/0.92       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.68/0.92  thf('5', plain,
% 0.68/0.92      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.68/0.92         ((r2_hidden @ X38 @ X39)
% 0.68/0.92          | ~ (r2_hidden @ (k4_tarski @ X38 @ X40) @ (k2_zfmisc_1 @ X39 @ X41)))),
% 0.68/0.92      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.68/0.92  thf('6', plain,
% 0.68/0.92      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_3)))
% 0.68/0.92         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.92  thf(d1_tarski, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.68/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.68/0.92  thf('7', plain,
% 0.68/0.92      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X24 @ X23)
% 0.68/0.92          | ((X24) = (X21))
% 0.68/0.92          | ((X23) != (k1_tarski @ X21)))),
% 0.68/0.92      inference('cnf', [status(esa)], [d1_tarski])).
% 0.68/0.92  thf('8', plain,
% 0.68/0.92      (![X21 : $i, X24 : $i]:
% 0.68/0.92         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['7'])).
% 0.68/0.92  thf('9', plain,
% 0.68/0.92      ((((sk_A) = (sk_C_3)))
% 0.68/0.92         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['6', '8'])).
% 0.68/0.92  thf('10', plain, ((((sk_A) != (sk_C_3))) <= (~ (((sk_A) = (sk_C_3))))),
% 0.68/0.92      inference('split', [status(esa)], ['0'])).
% 0.68/0.92  thf('11', plain,
% 0.68/0.92      ((((sk_A) != (sk_A)))
% 0.68/0.92         <= (~ (((sk_A) = (sk_C_3))) & 
% 0.68/0.92             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.92  thf('12', plain,
% 0.68/0.92      ((((sk_A) = (sk_C_3))) | 
% 0.68/0.92       ~
% 0.68/0.92       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))),
% 0.68/0.92      inference('simplify', [status(thm)], ['11'])).
% 0.68/0.92  thf('13', plain,
% 0.68/0.92      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))
% 0.68/0.92         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('split', [status(esa)], ['3'])).
% 0.68/0.92  thf('14', plain,
% 0.68/0.92      ((((sk_A) = (sk_C_3)))
% 0.68/0.92         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['6', '8'])).
% 0.68/0.92  thf('15', plain,
% 0.68/0.92      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D_2))))
% 0.68/0.92         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('demod', [status(thm)], ['13', '14'])).
% 0.68/0.92  thf('16', plain,
% 0.68/0.92      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.68/0.92         ((r2_hidden @ X40 @ X41)
% 0.68/0.92          | ~ (r2_hidden @ (k4_tarski @ X38 @ X40) @ (k2_zfmisc_1 @ X39 @ X41)))),
% 0.68/0.92      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.68/0.92  thf('17', plain,
% 0.68/0.92      (((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_D_2)))
% 0.68/0.92         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.92  thf('18', plain,
% 0.68/0.92      (![X21 : $i, X24 : $i]:
% 0.68/0.92         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['7'])).
% 0.68/0.92  thf('19', plain,
% 0.68/0.92      ((((sk_B_1) = (sk_D_2)))
% 0.68/0.92         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['17', '18'])).
% 0.68/0.92  thf('20', plain, ((((sk_B_1) != (sk_D_2))) <= (~ (((sk_B_1) = (sk_D_2))))),
% 0.68/0.92      inference('split', [status(esa)], ['0'])).
% 0.68/0.92  thf('21', plain,
% 0.68/0.92      ((((sk_B_1) != (sk_B_1)))
% 0.68/0.92         <= (~ (((sk_B_1) = (sk_D_2))) & 
% 0.68/0.92             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.92  thf('22', plain,
% 0.68/0.92      ((((sk_B_1) = (sk_D_2))) | 
% 0.68/0.92       ~
% 0.68/0.92       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))),
% 0.68/0.92      inference('simplify', [status(thm)], ['21'])).
% 0.68/0.92  thf('23', plain,
% 0.68/0.92      (~
% 0.68/0.92       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))),
% 0.68/0.92      inference('sat_resolution*', [status(thm)], ['2', '12', '22'])).
% 0.68/0.92  thf('24', plain,
% 0.68/0.92      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92          (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2)))),
% 0.68/0.92      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.68/0.92  thf('25', plain, ((((sk_A) = (sk_C_3))) <= ((((sk_A) = (sk_C_3))))),
% 0.68/0.92      inference('split', [status(esa)], ['3'])).
% 0.68/0.92  thf('26', plain,
% 0.68/0.92      ((((sk_A) = (sk_C_3))) | 
% 0.68/0.92       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))),
% 0.68/0.92      inference('split', [status(esa)], ['3'])).
% 0.68/0.92  thf('27', plain, ((((sk_A) = (sk_C_3)))),
% 0.68/0.92      inference('sat_resolution*', [status(thm)], ['2', '12', '22', '26'])).
% 0.68/0.92  thf('28', plain, (((sk_A) = (sk_C_3))),
% 0.68/0.92      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.68/0.92  thf('29', plain,
% 0.68/0.92      ((((sk_B_1) = (sk_D_2))
% 0.68/0.92        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92           (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('30', plain, ((((sk_B_1) = (sk_D_2))) <= ((((sk_B_1) = (sk_D_2))))),
% 0.68/0.92      inference('split', [status(esa)], ['29'])).
% 0.68/0.92  thf('31', plain,
% 0.68/0.92      ((((sk_B_1) = (sk_D_2))) | 
% 0.68/0.92       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ (k1_tarski @ sk_D_2))))),
% 0.68/0.92      inference('split', [status(esa)], ['29'])).
% 0.68/0.92  thf('32', plain, ((((sk_B_1) = (sk_D_2)))),
% 0.68/0.92      inference('sat_resolution*', [status(thm)], ['2', '12', '22', '31'])).
% 0.68/0.92  thf('33', plain, (((sk_B_1) = (sk_D_2))),
% 0.68/0.92      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 0.68/0.92  thf('34', plain,
% 0.68/0.92      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ 
% 0.68/0.92          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.68/0.92      inference('demod', [status(thm)], ['24', '28', '33'])).
% 0.68/0.92  thf(t7_xboole_0, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.68/0.92          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.68/0.92  thf('35', plain,
% 0.68/0.92      (![X20 : $i]:
% 0.68/0.92         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.68/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.68/0.92  thf('36', plain,
% 0.68/0.92      (![X20 : $i]:
% 0.68/0.92         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.68/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.68/0.92  thf(l33_zfmisc_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.68/0.92       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.68/0.92  thf('37', plain,
% 0.68/0.92      (![X35 : $i, X37 : $i]:
% 0.68/0.92         (((k4_xboole_0 @ (k1_tarski @ X35) @ X37) = (k1_tarski @ X35))
% 0.68/0.92          | (r2_hidden @ X35 @ X37))),
% 0.68/0.92      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.68/0.92  thf(d5_xboole_0, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i]:
% 0.68/0.92     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.68/0.92       ( ![D:$i]:
% 0.68/0.92         ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.92           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.68/0.92  thf('38', plain,
% 0.68/0.92      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X10 @ X9)
% 0.68/0.92          | ~ (r2_hidden @ X10 @ X8)
% 0.68/0.92          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.68/0.92      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.92  thf('39', plain,
% 0.68/0.92      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X10 @ X8)
% 0.68/0.92          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['38'])).
% 0.68/0.92  thf('40', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.68/0.92          | (r2_hidden @ X0 @ X1)
% 0.68/0.92          | ~ (r2_hidden @ X2 @ X1))),
% 0.68/0.92      inference('sup-', [status(thm)], ['37', '39'])).
% 0.68/0.92  thf('41', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.92          | ~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ X1)
% 0.68/0.92          | (r2_hidden @ X0 @ X1))),
% 0.68/0.92      inference('sup-', [status(thm)], ['36', '40'])).
% 0.68/0.92  thf(t3_xboole_0, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.68/0.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.68/0.92            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.68/0.92  thf('42', plain,
% 0.68/0.92      (![X12 : $i, X13 : $i]:
% 0.68/0.92         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X13))),
% 0.68/0.92      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.68/0.92  thf('43', plain,
% 0.68/0.92      (![X21 : $i, X24 : $i]:
% 0.68/0.92         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['7'])).
% 0.68/0.92  thf('44', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.68/0.92          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['42', '43'])).
% 0.68/0.92  thf('45', plain,
% 0.68/0.92      (![X12 : $i, X13 : $i]:
% 0.68/0.92         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X12))),
% 0.68/0.92      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.68/0.92  thf('46', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r2_hidden @ X0 @ X1)
% 0.68/0.92          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.68/0.92          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['44', '45'])).
% 0.68/0.92  thf('47', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.68/0.92      inference('simplify', [status(thm)], ['46'])).
% 0.68/0.92  thf('48', plain,
% 0.68/0.92      (![X20 : $i]:
% 0.68/0.92         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.68/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.68/0.92  thf(t4_xboole_0, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.68/0.92            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.68/0.92  thf('49', plain,
% 0.68/0.92      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 0.68/0.92          | ~ (r1_xboole_0 @ X16 @ X19))),
% 0.68/0.92      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.68/0.92  thf('50', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['48', '49'])).
% 0.68/0.92  thf('51', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r2_hidden @ X0 @ X1)
% 0.68/0.92          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['47', '50'])).
% 0.68/0.92  thf(l29_zfmisc_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.68/0.92       ( r2_hidden @ B @ A ) ))).
% 0.68/0.92  thf('52', plain,
% 0.68/0.92      (![X33 : $i, X34 : $i]:
% 0.68/0.92         ((r2_hidden @ X33 @ X34)
% 0.68/0.92          | ((k3_xboole_0 @ X34 @ (k1_tarski @ X33)) != (k1_tarski @ X33)))),
% 0.68/0.92      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.68/0.92  thf('53', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.68/0.92          | (r2_hidden @ X0 @ X1)
% 0.68/0.92          | (r2_hidden @ X0 @ X1))),
% 0.68/0.92      inference('sup-', [status(thm)], ['51', '52'])).
% 0.68/0.92  thf('54', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r2_hidden @ X0 @ X1) | ((k1_xboole_0) != (k1_tarski @ X0)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['53'])).
% 0.68/0.92  thf('55', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r2_hidden @ X0 @ X1)
% 0.68/0.92          | ~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ X1))),
% 0.68/0.92      inference('clc', [status(thm)], ['41', '54'])).
% 0.68/0.92  thf('56', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.92          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['35', '55'])).
% 0.68/0.92  thf('57', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r2_hidden @ X0 @ X1) | ((k1_xboole_0) != (k1_tarski @ X0)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['53'])).
% 0.68/0.92  thf('58', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.68/0.92      inference('clc', [status(thm)], ['56', '57'])).
% 0.68/0.92  thf('59', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.68/0.92      inference('clc', [status(thm)], ['56', '57'])).
% 0.68/0.92  thf('60', plain,
% 0.68/0.92      (![X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.68/0.92         ((r2_hidden @ (k4_tarski @ X38 @ X40) @ (k2_zfmisc_1 @ X39 @ X42))
% 0.68/0.92          | ~ (r2_hidden @ X40 @ X42)
% 0.68/0.92          | ~ (r2_hidden @ X38 @ X39))),
% 0.68/0.92      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.68/0.92  thf('61', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X2 @ X1)
% 0.68/0.92          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.68/0.92             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['59', '60'])).
% 0.68/0.92  thf('62', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.68/0.92          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['58', '61'])).
% 0.68/0.92  thf('63', plain, ($false), inference('demod', [status(thm)], ['34', '62'])).
% 0.68/0.92  
% 0.68/0.92  % SZS output end Refutation
% 0.68/0.92  
% 0.68/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
