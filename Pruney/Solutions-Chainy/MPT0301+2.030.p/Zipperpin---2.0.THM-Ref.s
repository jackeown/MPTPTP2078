%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lxv3ByFsTf

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 210 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  746 (1617 expanded)
%              Number of equality atoms :  115 ( 264 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t113_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
      <=> ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_zfmisc_1])).

thf('0',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ( X26
        = ( k2_zfmisc_1 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X26 @ X22 @ X23 ) @ ( sk_E @ X26 @ X22 @ X23 ) @ ( sk_D @ X26 @ X22 @ X23 ) @ X22 @ X23 )
      | ( r2_hidden @ ( sk_D @ X26 @ X22 @ X23 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('22',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('30',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X33 ) )
      | ~ ( r2_hidden @ X31 @ X33 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('41',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('46',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('49',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X25 @ X22 @ X23 ) @ ( sk_E_1 @ X25 @ X22 @ X23 ) @ X25 @ X22 @ X23 )
      | ( X24
       != ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X25 @ X22 @ X23 ) @ ( sk_E_1 @ X25 @ X22 @ X23 ) @ X25 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X13 @ X17 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('55',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('56',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('61',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('63',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','32','47','64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lxv3ByFsTf
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 217 iterations in 0.066s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.21/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(t113_zfmisc_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((((sk_B_1) != (k1_xboole_0))
% 0.21/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.52       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf(d2_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ?[E:$i,F:$i]:
% 0.21/0.52             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.52               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_2, axiom,
% 0.21/0.52    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.52       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.52         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.52  thf(zf_stmt_3, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i, X26 : $i]:
% 0.21/0.52         (((X26) = (k2_zfmisc_1 @ X23 @ X22))
% 0.21/0.52          | (zip_tseitin_0 @ (sk_F @ X26 @ X22 @ X23) @ 
% 0.21/0.52             (sk_E @ X26 @ X22 @ X23) @ (sk_D @ X26 @ X22 @ X23) @ X22 @ X23)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X26 @ X22 @ X23) @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         ((r2_hidden @ X14 @ X16)
% 0.21/0.52          | ~ (zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.21/0.52          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.52          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(t17_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.21/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.52  thf(t3_xboole_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t4_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t100_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X5 @ X6)
% 0.21/0.52           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.52           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf(t5_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('13', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf(t79_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.21/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.52  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.21/0.52          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('21', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '16'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 0.21/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.21/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((![X0 : $i]: ((sk_B_1) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.21/0.52         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((((sk_A) != (k1_xboole_0))
% 0.21/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((sk_B_1) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.52             (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((((sk_B_1) != (sk_B_1)))
% 0.21/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.52             (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.52       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.52       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('split', [status(esa)], ['26'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.52         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf(t7_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf(l54_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 0.21/0.52         ((r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X33))
% 0.21/0.52          | ~ (r2_hidden @ X31 @ X33)
% 0.21/0.52          | ~ (r2_hidden @ X29 @ X30))),
% 0.21/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X2 @ X1)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.21/0.52             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((X0) = (k1_xboole_0))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.21/0.52             (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.52          | ((X1) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.52          k1_xboole_0)
% 0.21/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.52         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['33', '38'])).
% 0.21/0.52  thf('40', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '16'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.52         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.52         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.52             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.52         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.52             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['26'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((((sk_A) != (sk_A)))
% 0.21/0.52         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.52             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.21/0.52             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) | 
% 0.21/0.52       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.52       (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X25 @ X24)
% 0.21/0.52          | (zip_tseitin_0 @ (sk_F_1 @ X25 @ X22 @ X23) @ 
% 0.21/0.52             (sk_E_1 @ X25 @ X22 @ X23) @ X25 @ X22 @ X23)
% 0.21/0.52          | ((X24) != (k2_zfmisc_1 @ X23 @ X22)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ (sk_F_1 @ X25 @ X22 @ X23) @ 
% 0.21/0.52           (sk_E_1 @ X25 @ X22 @ X23) @ X25 @ X22 @ X23)
% 0.21/0.52          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X23 @ X22)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.52          | (zip_tseitin_0 @ 
% 0.21/0.52             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.52             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.52             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         ((r2_hidden @ X13 @ X17)
% 0.21/0.52          | ~ (zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('55', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '16'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['53', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      ((![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A)))
% 0.21/0.52         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['26'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      ((((sk_A) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.52             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((((sk_A) != (sk_A)))
% 0.21/0.52         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.52             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.52       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) | 
% 0.21/0.52       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.21/0.52       (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('66', plain, ($false),
% 0.21/0.52      inference('sat_resolution*', [status(thm)],
% 0.21/0.52                ['1', '31', '32', '47', '64', '65'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
