%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B9aMoyPtcJ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:43 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 198 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  811 (1953 expanded)
%              Number of equality atoms :   55 ( 130 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X28 @ X30 ) @ ( k3_xboole_0 @ X29 @ X31 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('7',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X28 @ X30 ) @ ( k3_xboole_0 @ X29 @ X31 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      | ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X28 @ X30 ) @ ( k3_xboole_0 @ X29 @ X31 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_zfmisc_1 @ X20 @ X21 )
        = k1_xboole_0 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,(
    ! [X21: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['34','36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X28 @ X30 ) @ ( k3_xboole_0 @ X29 @ X31 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('47',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('49',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X23 @ X22 ) @ ( k2_zfmisc_1 @ X24 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) )
      | ( ( k3_xboole_0 @ sk_B @ sk_D_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_D_1 )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('53',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_D_1 )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('64',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_zfmisc_1 @ X20 @ X21 )
        = k1_xboole_0 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['64','66'])).

thf('68',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['69','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['41','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B9aMoyPtcJ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.52/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.75  % Solved by: fo/fo7.sh
% 0.52/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.75  % done 494 iterations in 0.295s
% 0.52/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.75  % SZS output start Refutation
% 0.52/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.52/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.75  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.75  thf(t138_zfmisc_1, conjecture,
% 0.52/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.75     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.52/0.75       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.75         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.52/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.75        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.52/0.75          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.75            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.52/0.75    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.52/0.75  thf('0', plain,
% 0.52/0.75      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('1', plain,
% 0.52/0.75      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.52/0.75      inference('split', [status(esa)], ['0'])).
% 0.52/0.75  thf(d3_tarski, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.75  thf('2', plain,
% 0.52/0.75      (![X1 : $i, X3 : $i]:
% 0.52/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.75  thf('3', plain,
% 0.52/0.75      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.75        (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(t28_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.75  thf('4', plain,
% 0.52/0.75      (![X16 : $i, X17 : $i]:
% 0.52/0.75         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.52/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.75  thf('5', plain,
% 0.52/0.75      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.75         (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.75  thf(t123_zfmisc_1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.75     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.52/0.75       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.52/0.75  thf('6', plain,
% 0.52/0.75      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X28 @ X30) @ (k3_xboole_0 @ X29 @ X31))
% 0.52/0.75           = (k3_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 0.52/0.75              (k2_zfmisc_1 @ X30 @ X31)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.52/0.75  thf('7', plain,
% 0.52/0.75      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.52/0.75         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['5', '6'])).
% 0.52/0.75  thf(d10_xboole_0, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.75  thf('8', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.52/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.75  thf('9', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.52/0.75      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.75  thf('10', plain,
% 0.52/0.75      (![X16 : $i, X17 : $i]:
% 0.52/0.75         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.52/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.75  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.75  thf('12', plain,
% 0.52/0.75      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X28 @ X30) @ (k3_xboole_0 @ X29 @ X31))
% 0.52/0.75           = (k3_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 0.52/0.75              (k2_zfmisc_1 @ X30 @ X31)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.52/0.75  thf(d4_xboole_0, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.52/0.75       ( ![D:$i]:
% 0.52/0.75         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.75           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.52/0.75  thf('13', plain,
% 0.52/0.75      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X8 @ X7)
% 0.52/0.75          | (r2_hidden @ X8 @ X6)
% 0.52/0.75          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.75  thf('14', plain,
% 0.52/0.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.52/0.75         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.75      inference('simplify', [status(thm)], ['13'])).
% 0.52/0.75  thf('15', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X4 @ 
% 0.52/0.75             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.52/0.75          | (r2_hidden @ X4 @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['12', '14'])).
% 0.52/0.75  thf('16', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1)))
% 0.52/0.75          | (r2_hidden @ X3 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['11', '15'])).
% 0.52/0.75  thf('17', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.52/0.75          | (r2_hidden @ X0 @ 
% 0.52/0.75             (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ sk_D_1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['7', '16'])).
% 0.52/0.75  thf('18', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 0.52/0.75          | (r2_hidden @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 0.52/0.75             (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ sk_D_1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['2', '17'])).
% 0.52/0.75  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.75  thf('20', plain,
% 0.52/0.75      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X28 @ X30) @ (k3_xboole_0 @ X29 @ X31))
% 0.52/0.75           = (k3_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 0.52/0.75              (k2_zfmisc_1 @ X30 @ X31)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.52/0.75  thf('21', plain,
% 0.52/0.75      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X8 @ X7)
% 0.52/0.75          | (r2_hidden @ X8 @ X5)
% 0.52/0.75          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.75  thf('22', plain,
% 0.52/0.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.52/0.75         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.75      inference('simplify', [status(thm)], ['21'])).
% 0.52/0.75  thf('23', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X4 @ 
% 0.52/0.75             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.52/0.75          | (r2_hidden @ X4 @ (k2_zfmisc_1 @ X3 @ X1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['20', '22'])).
% 0.52/0.75  thf('24', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.52/0.75          | (r2_hidden @ X3 @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['19', '23'])).
% 0.52/0.75  thf('25', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 0.52/0.75          | (r2_hidden @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 0.52/0.75             (k2_zfmisc_1 @ sk_A @ sk_D_1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['18', '24'])).
% 0.52/0.75  thf('26', plain,
% 0.52/0.75      (![X1 : $i, X3 : $i]:
% 0.52/0.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.75  thf('27', plain,
% 0.52/0.75      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.75         (k2_zfmisc_1 @ sk_A @ sk_D_1))
% 0.52/0.75        | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.75           (k2_zfmisc_1 @ sk_A @ sk_D_1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.52/0.75  thf('28', plain,
% 0.52/0.75      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 0.52/0.75      inference('simplify', [status(thm)], ['27'])).
% 0.52/0.75  thf(t117_zfmisc_1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.75          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.52/0.75            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.52/0.75          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.52/0.75  thf('29', plain,
% 0.52/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.75         (((X22) = (k1_xboole_0))
% 0.52/0.75          | (r1_tarski @ X23 @ X24)
% 0.52/0.75          | ~ (r1_tarski @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 0.52/0.75               (k2_zfmisc_1 @ X22 @ X24)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.52/0.75  thf('30', plain, (((r1_tarski @ sk_B @ sk_D_1) | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.75  thf('31', plain,
% 0.52/0.75      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.52/0.75      inference('split', [status(esa)], ['0'])).
% 0.52/0.75  thf('32', plain,
% 0.52/0.75      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.75  thf('33', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('34', plain,
% 0.52/0.75      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.52/0.75         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['32', '33'])).
% 0.52/0.75  thf(t113_zfmisc_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.75  thf('35', plain,
% 0.52/0.75      (![X20 : $i, X21 : $i]:
% 0.52/0.75         (((k2_zfmisc_1 @ X20 @ X21) = (k1_xboole_0))
% 0.52/0.75          | ((X20) != (k1_xboole_0)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.75  thf('36', plain,
% 0.52/0.75      (![X21 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 0.52/0.75      inference('simplify', [status(thm)], ['35'])).
% 0.52/0.75  thf('37', plain,
% 0.52/0.75      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.52/0.75      inference('demod', [status(thm)], ['34', '36'])).
% 0.52/0.75  thf('38', plain, (((r1_tarski @ sk_B @ sk_D_1))),
% 0.52/0.75      inference('simplify', [status(thm)], ['37'])).
% 0.52/0.75  thf('39', plain,
% 0.52/0.75      (~ ((r1_tarski @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_B @ sk_D_1))),
% 0.52/0.75      inference('split', [status(esa)], ['0'])).
% 0.52/0.75  thf('40', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.52/0.75      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.52/0.75  thf('41', plain, (~ (r1_tarski @ sk_A @ sk_C_1)),
% 0.52/0.75      inference('simpl_trail', [status(thm)], ['1', '40'])).
% 0.52/0.75  thf('42', plain,
% 0.52/0.75      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 0.52/0.75      inference('simplify', [status(thm)], ['27'])).
% 0.52/0.75  thf('43', plain,
% 0.52/0.75      (![X16 : $i, X17 : $i]:
% 0.52/0.75         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.52/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.75  thf('44', plain,
% 0.52/0.75      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.75         (k2_zfmisc_1 @ sk_A @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.75      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.75  thf('45', plain,
% 0.52/0.75      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X28 @ X30) @ (k3_xboole_0 @ X29 @ X31))
% 0.52/0.75           = (k3_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 0.52/0.75              (k2_zfmisc_1 @ X30 @ X31)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.52/0.75  thf('46', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.75  thf('47', plain,
% 0.52/0.75      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D_1))
% 0.52/0.75         = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.52/0.75  thf('48', plain,
% 0.52/0.75      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.52/0.75         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['5', '6'])).
% 0.52/0.75  thf('49', plain,
% 0.52/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.75         (((X22) = (k1_xboole_0))
% 0.52/0.75          | (r1_tarski @ X23 @ X24)
% 0.52/0.75          | ~ (r1_tarski @ (k2_zfmisc_1 @ X23 @ X22) @ 
% 0.52/0.75               (k2_zfmisc_1 @ X24 @ X22)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.52/0.75  thf('50', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_B @ sk_D_1)) @ 
% 0.52/0.75             (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.52/0.75          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_A @ sk_C_1))
% 0.52/0.75          | ((k3_xboole_0 @ sk_B @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.75  thf('51', plain,
% 0.52/0.75      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.75           (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.52/0.75        | ((k3_xboole_0 @ sk_B @ sk_D_1) = (k1_xboole_0))
% 0.52/0.75        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['47', '50'])).
% 0.52/0.75  thf('52', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.52/0.75      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.75  thf('53', plain,
% 0.52/0.75      ((((k3_xboole_0 @ sk_B @ sk_D_1) = (k1_xboole_0))
% 0.52/0.75        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 0.52/0.75      inference('demod', [status(thm)], ['51', '52'])).
% 0.52/0.75  thf('54', plain,
% 0.52/0.75      (![X1 : $i, X3 : $i]:
% 0.52/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.75  thf('55', plain,
% 0.52/0.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.52/0.75         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.75      inference('simplify', [status(thm)], ['21'])).
% 0.52/0.75  thf('56', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.75         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.75          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.52/0.75      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.75  thf('57', plain,
% 0.52/0.75      (![X1 : $i, X3 : $i]:
% 0.52/0.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.75  thf('58', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.52/0.75          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.75  thf('59', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.52/0.75      inference('simplify', [status(thm)], ['58'])).
% 0.52/0.75  thf('60', plain,
% 0.52/0.75      (![X10 : $i, X12 : $i]:
% 0.52/0.75         (((X10) = (X12))
% 0.52/0.75          | ~ (r1_tarski @ X12 @ X10)
% 0.52/0.75          | ~ (r1_tarski @ X10 @ X12))),
% 0.52/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.75  thf('61', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.52/0.75          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['59', '60'])).
% 0.52/0.75  thf('62', plain,
% 0.52/0.75      ((((k3_xboole_0 @ sk_B @ sk_D_1) = (k1_xboole_0))
% 0.52/0.75        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['53', '61'])).
% 0.52/0.75  thf('63', plain,
% 0.52/0.75      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.52/0.75         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['5', '6'])).
% 0.52/0.75  thf('64', plain,
% 0.52/0.75      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ k1_xboole_0)
% 0.52/0.75          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.52/0.75        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['62', '63'])).
% 0.52/0.75  thf('65', plain,
% 0.52/0.75      (![X20 : $i, X21 : $i]:
% 0.52/0.75         (((k2_zfmisc_1 @ X20 @ X21) = (k1_xboole_0))
% 0.52/0.75          | ((X21) != (k1_xboole_0)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.75  thf('66', plain,
% 0.52/0.75      (![X20 : $i]: ((k2_zfmisc_1 @ X20 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.75      inference('simplify', [status(thm)], ['65'])).
% 0.52/0.75  thf('67', plain,
% 0.52/0.75      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.52/0.75        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 0.52/0.75      inference('demod', [status(thm)], ['64', '66'])).
% 0.52/0.75  thf('68', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('69', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.52/0.75      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.52/0.75  thf('70', plain,
% 0.52/0.75      (![X1 : $i, X3 : $i]:
% 0.52/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.75  thf('71', plain,
% 0.52/0.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.52/0.75         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.75      inference('simplify', [status(thm)], ['13'])).
% 0.52/0.75  thf('72', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.75         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.75          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['70', '71'])).
% 0.52/0.75  thf('73', plain,
% 0.52/0.75      (![X1 : $i, X3 : $i]:
% 0.52/0.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.75  thf('74', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.52/0.75          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['72', '73'])).
% 0.52/0.75  thf('75', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.52/0.75      inference('simplify', [status(thm)], ['74'])).
% 0.52/0.75  thf('76', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.52/0.75      inference('sup+', [status(thm)], ['69', '75'])).
% 0.52/0.75  thf('77', plain, ($false), inference('demod', [status(thm)], ['41', '76'])).
% 0.52/0.75  
% 0.52/0.75  % SZS output end Refutation
% 0.52/0.75  
% 0.52/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
