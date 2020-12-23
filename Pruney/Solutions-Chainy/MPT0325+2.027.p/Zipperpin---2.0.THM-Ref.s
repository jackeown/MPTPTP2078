%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8uaxkByDoP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:43 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 210 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   25
%              Number of atoms          :  694 (2061 expanded)
%              Number of equality atoms :   55 ( 118 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X28 @ X26 ) @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('19',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X24 @ X23 ) @ ( k2_zfmisc_1 @ X25 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('48',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['44'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_zfmisc_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X22: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['52','54'])).

thf('56',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['44'])).

thf('58',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['45','58'])).

thf('60',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['43','59'])).

thf('61',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_zfmisc_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','64'])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('68',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','66','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8uaxkByDoP
% 0.13/0.37  % Computer   : n017.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:25:46 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 725 iterations in 0.332s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.82  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.59/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.82  thf(t138_zfmisc_1, conjecture,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.82     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.59/0.82       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.82         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.82        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.59/0.82          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.82            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.59/0.82    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.59/0.82  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('1', plain,
% 0.59/0.82      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.59/0.82        (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(t28_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.82  thf('2', plain,
% 0.59/0.82      (![X16 : $i, X17 : $i]:
% 0.59/0.82         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.59/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.82  thf('3', plain,
% 0.59/0.82      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.59/0.82         (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.59/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.82  thf(t123_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.82     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.59/0.82       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.59/0.82  thf('4', plain,
% 0.59/0.82      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.59/0.82         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 0.59/0.82           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 0.59/0.82              (k2_zfmisc_1 @ X31 @ X32)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.59/0.82  thf('5', plain,
% 0.59/0.82      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.59/0.82         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.59/0.82      inference('demod', [status(thm)], ['3', '4'])).
% 0.59/0.82  thf(d3_tarski, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.82  thf('6', plain,
% 0.59/0.82      (![X1 : $i, X3 : $i]:
% 0.59/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.82  thf(d4_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.59/0.82       ( ![D:$i]:
% 0.59/0.82         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.82           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.82  thf('7', plain,
% 0.59/0.82      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X8 @ X7)
% 0.59/0.82          | (r2_hidden @ X8 @ X6)
% 0.59/0.82          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.59/0.82      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.59/0.82  thf('8', plain,
% 0.59/0.82      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.59/0.82         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['7'])).
% 0.59/0.82  thf('9', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.59/0.82          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['6', '8'])).
% 0.59/0.82  thf('10', plain,
% 0.59/0.82      (![X1 : $i, X3 : $i]:
% 0.59/0.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.82  thf('11', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.59/0.82          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.82  thf('12', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.59/0.82      inference('simplify', [status(thm)], ['11'])).
% 0.59/0.82  thf(t118_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( r1_tarski @ A @ B ) =>
% 0.59/0.82       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.59/0.82         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.59/0.82  thf('13', plain,
% 0.59/0.82      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.82         (~ (r1_tarski @ X26 @ X27)
% 0.59/0.82          | (r1_tarski @ (k2_zfmisc_1 @ X28 @ X26) @ (k2_zfmisc_1 @ X28 @ X27)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.59/0.82  thf('14', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.59/0.82          (k2_zfmisc_1 @ X2 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.82  thf('15', plain,
% 0.59/0.82      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.59/0.82        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ sk_D_1))),
% 0.59/0.82      inference('sup+', [status(thm)], ['5', '14'])).
% 0.59/0.82  thf('16', plain,
% 0.59/0.82      (![X16 : $i, X17 : $i]:
% 0.59/0.82         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.59/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.82  thf('17', plain,
% 0.59/0.82      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.59/0.82         (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ sk_D_1))
% 0.59/0.82         = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.59/0.82      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.82  thf('18', plain,
% 0.59/0.82      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.59/0.82         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 0.59/0.82           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 0.59/0.82              (k2_zfmisc_1 @ X31 @ X32)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.59/0.82  thf('19', plain,
% 0.59/0.82      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C_1)) @ 
% 0.59/0.82         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.59/0.82      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.82  thf('20', plain,
% 0.59/0.82      (![X1 : $i, X3 : $i]:
% 0.59/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.82  thf('21', plain,
% 0.59/0.82      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X8 @ X7)
% 0.59/0.82          | (r2_hidden @ X8 @ X5)
% 0.59/0.82          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.59/0.82      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.59/0.82  thf('22', plain,
% 0.59/0.82      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.59/0.82         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['21'])).
% 0.59/0.82  thf('23', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.59/0.82          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.59/0.82      inference('sup-', [status(thm)], ['20', '22'])).
% 0.59/0.82  thf('24', plain,
% 0.59/0.82      (![X1 : $i, X3 : $i]:
% 0.59/0.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.82  thf('25', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.59/0.82          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.82  thf('26', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.59/0.82      inference('simplify', [status(thm)], ['25'])).
% 0.59/0.82  thf('27', plain,
% 0.59/0.82      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.82         (~ (r1_tarski @ X26 @ X27)
% 0.59/0.82          | (r1_tarski @ (k2_zfmisc_1 @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.59/0.82  thf('28', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 0.59/0.82          (k2_zfmisc_1 @ X0 @ X2))),
% 0.59/0.82      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.82  thf('29', plain,
% 0.59/0.82      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.59/0.82        (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['19', '28'])).
% 0.59/0.82  thf(t117_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.59/0.82          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.59/0.82            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.59/0.82          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.59/0.82  thf('30', plain,
% 0.59/0.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.59/0.82         (((X23) = (k1_xboole_0))
% 0.59/0.82          | (r1_tarski @ X24 @ X25)
% 0.59/0.82          | ~ (r1_tarski @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 0.59/0.82               (k2_zfmisc_1 @ X23 @ X25)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.59/0.82  thf('31', plain,
% 0.59/0.82      (((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D_1))
% 0.59/0.82        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.82  thf('32', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.59/0.82      inference('simplify', [status(thm)], ['25'])).
% 0.59/0.82  thf(d10_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.82  thf('33', plain,
% 0.59/0.82      (![X10 : $i, X12 : $i]:
% 0.59/0.82         (((X10) = (X12))
% 0.59/0.82          | ~ (r1_tarski @ X12 @ X10)
% 0.59/0.82          | ~ (r1_tarski @ X10 @ X12))),
% 0.59/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.82  thf('34', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.59/0.82          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.82  thf('35', plain,
% 0.59/0.82      ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['31', '34'])).
% 0.59/0.82  thf('36', plain,
% 0.59/0.82      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.59/0.82         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.59/0.82      inference('demod', [status(thm)], ['3', '4'])).
% 0.59/0.82  thf('37', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.59/0.82      inference('simplify', [status(thm)], ['11'])).
% 0.59/0.82  thf('38', plain,
% 0.59/0.82      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.82         (~ (r1_tarski @ X26 @ X27)
% 0.59/0.82          | (r1_tarski @ (k2_zfmisc_1 @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.59/0.82  thf('39', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 0.59/0.82          (k2_zfmisc_1 @ X0 @ X2))),
% 0.59/0.82      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.82  thf('40', plain,
% 0.59/0.82      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.59/0.82        (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['36', '39'])).
% 0.59/0.82  thf('41', plain,
% 0.59/0.82      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.59/0.82         (k2_zfmisc_1 @ sk_C_1 @ sk_B))
% 0.59/0.82        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['35', '40'])).
% 0.59/0.82  thf('42', plain,
% 0.59/0.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.59/0.82         (((X23) = (k1_xboole_0))
% 0.59/0.82          | (r1_tarski @ X24 @ X25)
% 0.59/0.82          | ~ (r1_tarski @ (k2_zfmisc_1 @ X24 @ X23) @ 
% 0.59/0.82               (k2_zfmisc_1 @ X25 @ X23)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.59/0.82  thf('43', plain,
% 0.59/0.82      ((((sk_A) = (k1_xboole_0))
% 0.59/0.82        | (r1_tarski @ sk_A @ sk_C_1)
% 0.59/0.82        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.82  thf('44', plain,
% 0.59/0.82      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('45', plain,
% 0.59/0.82      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.59/0.82      inference('split', [status(esa)], ['44'])).
% 0.59/0.82  thf('46', plain,
% 0.59/0.82      ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['31', '34'])).
% 0.59/0.82  thf('47', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.59/0.82      inference('simplify', [status(thm)], ['11'])).
% 0.59/0.82  thf('48', plain, (((r1_tarski @ sk_B @ sk_D_1) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['46', '47'])).
% 0.59/0.82  thf('49', plain,
% 0.59/0.82      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.59/0.82      inference('split', [status(esa)], ['44'])).
% 0.59/0.82  thf('50', plain,
% 0.59/0.82      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.82  thf('51', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('52', plain,
% 0.59/0.82      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.59/0.82         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.82  thf(t113_zfmisc_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.82  thf('53', plain,
% 0.59/0.82      (![X21 : $i, X22 : $i]:
% 0.59/0.82         (((k2_zfmisc_1 @ X21 @ X22) = (k1_xboole_0))
% 0.59/0.82          | ((X21) != (k1_xboole_0)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.82  thf('54', plain,
% 0.59/0.82      (![X22 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.82  thf('55', plain,
% 0.59/0.82      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.59/0.82      inference('demod', [status(thm)], ['52', '54'])).
% 0.59/0.82  thf('56', plain, (((r1_tarski @ sk_B @ sk_D_1))),
% 0.59/0.82      inference('simplify', [status(thm)], ['55'])).
% 0.59/0.82  thf('57', plain,
% 0.59/0.82      (~ ((r1_tarski @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_B @ sk_D_1))),
% 0.59/0.82      inference('split', [status(esa)], ['44'])).
% 0.59/0.82  thf('58', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.59/0.82  thf('59', plain, (~ (r1_tarski @ sk_A @ sk_C_1)),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['45', '58'])).
% 0.59/0.82  thf('60', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.82      inference('clc', [status(thm)], ['43', '59'])).
% 0.59/0.82  thf('61', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('62', plain,
% 0.59/0.82      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.59/0.82        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.82  thf('63', plain,
% 0.59/0.82      (![X21 : $i, X22 : $i]:
% 0.59/0.82         (((k2_zfmisc_1 @ X21 @ X22) = (k1_xboole_0))
% 0.59/0.82          | ((X22) != (k1_xboole_0)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.82  thf('64', plain,
% 0.59/0.82      (![X21 : $i]: ((k2_zfmisc_1 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['63'])).
% 0.59/0.82  thf('65', plain,
% 0.59/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.82      inference('demod', [status(thm)], ['62', '64'])).
% 0.59/0.82  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['65'])).
% 0.59/0.82  thf('67', plain,
% 0.59/0.82      (![X22 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.82  thf('68', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.59/0.82      inference('demod', [status(thm)], ['0', '66', '67'])).
% 0.59/0.82  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.59/0.82  
% 0.59/0.82  % SZS output end Refutation
% 0.59/0.82  
% 0.65/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
