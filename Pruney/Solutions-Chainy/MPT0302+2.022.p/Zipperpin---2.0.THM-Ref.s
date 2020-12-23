%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FEwMfgEGj1

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:08 EST 2020

% Result     : Theorem 13.80s
% Output     : Refutation 13.80s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 252 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   25
%              Number of atoms          :  674 (2021 expanded)
%              Number of equality atoms :   55 ( 221 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X27: $i] :
      ( ( X27
        = ( k3_tarski @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X27 @ X23 ) @ X23 )
      | ( r2_hidden @ ( sk_C_3 @ X27 @ X23 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('3',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('19',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('20',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('22',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X33 ) )
      | ~ ( r2_hidden @ X31 @ X33 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_3 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_3 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('27',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['34'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('37',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('41',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_3 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C_3 @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ ( sk_C_3 @ sk_B @ k1_xboole_0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ ( sk_C_3 @ sk_B @ k1_xboole_0 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X33 ) )
      | ~ ( r2_hidden @ X31 @ X33 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_3 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ ( sk_C_3 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','59'])).

thf('61',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ ( sk_C_3 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('64',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('66',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FEwMfgEGj1
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 13.80/14.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.80/14.01  % Solved by: fo/fo7.sh
% 13.80/14.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.80/14.01  % done 4373 iterations in 13.566s
% 13.80/14.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.80/14.01  % SZS output start Refutation
% 13.80/14.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 13.80/14.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.80/14.01  thf(sk_B_type, type, sk_B: $i).
% 13.80/14.01  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 13.80/14.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.80/14.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 13.80/14.01  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 13.80/14.01  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.80/14.01  thf(sk_A_type, type, sk_A: $i).
% 13.80/14.01  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 13.80/14.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.80/14.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.80/14.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.80/14.01  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 13.80/14.01  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 13.80/14.01  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 13.80/14.01  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 13.80/14.01  thf(d3_tarski, axiom,
% 13.80/14.01    (![A:$i,B:$i]:
% 13.80/14.01     ( ( r1_tarski @ A @ B ) <=>
% 13.80/14.01       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 13.80/14.01  thf('0', plain,
% 13.80/14.01      (![X1 : $i, X3 : $i]:
% 13.80/14.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 13.80/14.01      inference('cnf', [status(esa)], [d3_tarski])).
% 13.80/14.01  thf(d4_tarski, axiom,
% 13.80/14.01    (![A:$i,B:$i]:
% 13.80/14.01     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 13.80/14.01       ( ![C:$i]:
% 13.80/14.01         ( ( r2_hidden @ C @ B ) <=>
% 13.80/14.01           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 13.80/14.01  thf('1', plain,
% 13.80/14.01      (![X23 : $i, X27 : $i]:
% 13.80/14.01         (((X27) = (k3_tarski @ X23))
% 13.80/14.01          | (r2_hidden @ (sk_D @ X27 @ X23) @ X23)
% 13.80/14.01          | (r2_hidden @ (sk_C_3 @ X27 @ X23) @ X27))),
% 13.80/14.01      inference('cnf', [status(esa)], [d4_tarski])).
% 13.80/14.01  thf(t92_xboole_1, axiom,
% 13.80/14.01    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 13.80/14.01  thf('2', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 13.80/14.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 13.80/14.01  thf('3', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 13.80/14.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 13.80/14.01  thf(t91_xboole_1, axiom,
% 13.80/14.01    (![A:$i,B:$i,C:$i]:
% 13.80/14.01     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 13.80/14.01       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 13.80/14.01  thf('4', plain,
% 13.80/14.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 13.80/14.01         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 13.80/14.01           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 13.80/14.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 13.80/14.01  thf('5', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i]:
% 13.80/14.01         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 13.80/14.01           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 13.80/14.01      inference('sup+', [status(thm)], ['3', '4'])).
% 13.80/14.01  thf('6', plain,
% 13.80/14.01      (![X0 : $i]:
% 13.80/14.01         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 13.80/14.01      inference('sup+', [status(thm)], ['2', '5'])).
% 13.80/14.01  thf(t5_boole, axiom,
% 13.80/14.01    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 13.80/14.01  thf('7', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 13.80/14.01      inference('cnf', [status(esa)], [t5_boole])).
% 13.80/14.01  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 13.80/14.01      inference('demod', [status(thm)], ['6', '7'])).
% 13.80/14.01  thf(t95_xboole_1, axiom,
% 13.80/14.01    (![A:$i,B:$i]:
% 13.80/14.01     ( ( k3_xboole_0 @ A @ B ) =
% 13.80/14.01       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 13.80/14.01  thf('9', plain,
% 13.80/14.01      (![X20 : $i, X21 : $i]:
% 13.80/14.01         ((k3_xboole_0 @ X20 @ X21)
% 13.80/14.01           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 13.80/14.01              (k2_xboole_0 @ X20 @ X21)))),
% 13.80/14.01      inference('cnf', [status(esa)], [t95_xboole_1])).
% 13.80/14.01  thf('10', plain,
% 13.80/14.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 13.80/14.01         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 13.80/14.01           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 13.80/14.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 13.80/14.01  thf('11', plain,
% 13.80/14.01      (![X20 : $i, X21 : $i]:
% 13.80/14.01         ((k3_xboole_0 @ X20 @ X21)
% 13.80/14.01           = (k5_xboole_0 @ X20 @ 
% 13.80/14.01              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 13.80/14.01      inference('demod', [status(thm)], ['9', '10'])).
% 13.80/14.01  thf('12', plain,
% 13.80/14.01      (![X0 : $i]:
% 13.80/14.01         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 13.80/14.01           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 13.80/14.01      inference('sup+', [status(thm)], ['8', '11'])).
% 13.80/14.01  thf(t1_boole, axiom,
% 13.80/14.01    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 13.80/14.01  thf('13', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 13.80/14.01      inference('cnf', [status(esa)], [t1_boole])).
% 13.80/14.01  thf('14', plain,
% 13.80/14.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 13.80/14.01      inference('demod', [status(thm)], ['12', '13'])).
% 13.80/14.01  thf('15', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 13.80/14.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 13.80/14.01  thf('16', plain,
% 13.80/14.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 13.80/14.01      inference('demod', [status(thm)], ['14', '15'])).
% 13.80/14.01  thf(t4_xboole_0, axiom,
% 13.80/14.01    (![A:$i,B:$i]:
% 13.80/14.01     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 13.80/14.01            ( r1_xboole_0 @ A @ B ) ) ) & 
% 13.80/14.01       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 13.80/14.01            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 13.80/14.01  thf('17', plain,
% 13.80/14.01      (![X7 : $i, X9 : $i, X10 : $i]:
% 13.80/14.01         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 13.80/14.01          | ~ (r1_xboole_0 @ X7 @ X10))),
% 13.80/14.01      inference('cnf', [status(esa)], [t4_xboole_0])).
% 13.80/14.01  thf('18', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i]:
% 13.80/14.01         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 13.80/14.01      inference('sup-', [status(thm)], ['16', '17'])).
% 13.80/14.01  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 13.80/14.01  thf('19', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 13.80/14.01      inference('cnf', [status(esa)], [t65_xboole_1])).
% 13.80/14.01  thf('20', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 13.80/14.01      inference('demod', [status(thm)], ['18', '19'])).
% 13.80/14.01  thf('21', plain,
% 13.80/14.01      (![X0 : $i]:
% 13.80/14.01         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 13.80/14.01          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 13.80/14.01      inference('sup-', [status(thm)], ['1', '20'])).
% 13.80/14.01  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 13.80/14.01  thf('22', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 13.80/14.01      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 13.80/14.01  thf('23', plain,
% 13.80/14.01      (![X0 : $i]:
% 13.80/14.01         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 13.80/14.01          | ((X0) = (k1_xboole_0)))),
% 13.80/14.01      inference('demod', [status(thm)], ['21', '22'])).
% 13.80/14.01  thf(l54_zfmisc_1, axiom,
% 13.80/14.01    (![A:$i,B:$i,C:$i,D:$i]:
% 13.80/14.01     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 13.80/14.01       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 13.80/14.01  thf('24', plain,
% 13.80/14.01      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 13.80/14.01         ((r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X33))
% 13.80/14.01          | ~ (r2_hidden @ X31 @ X33)
% 13.80/14.01          | ~ (r2_hidden @ X29 @ X30))),
% 13.80/14.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 13.80/14.01  thf('25', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.80/14.01         (((X0) = (k1_xboole_0))
% 13.80/14.01          | ~ (r2_hidden @ X2 @ X1)
% 13.80/14.01          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_3 @ X0 @ k1_xboole_0)) @ 
% 13.80/14.01             (k2_zfmisc_1 @ X1 @ X0)))),
% 13.80/14.01      inference('sup-', [status(thm)], ['23', '24'])).
% 13.80/14.01  thf('26', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.80/14.01         ((r1_tarski @ X0 @ X1)
% 13.80/14.01          | (r2_hidden @ 
% 13.80/14.01             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_3 @ X2 @ k1_xboole_0)) @ 
% 13.80/14.01             (k2_zfmisc_1 @ X0 @ X2))
% 13.80/14.01          | ((X2) = (k1_xboole_0)))),
% 13.80/14.01      inference('sup-', [status(thm)], ['0', '25'])).
% 13.80/14.01  thf(t114_zfmisc_1, conjecture,
% 13.80/14.01    (![A:$i,B:$i]:
% 13.80/14.01     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 13.80/14.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 13.80/14.01         ( ( A ) = ( B ) ) ) ))).
% 13.80/14.01  thf(zf_stmt_0, negated_conjecture,
% 13.80/14.01    (~( ![A:$i,B:$i]:
% 13.80/14.01        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 13.80/14.01          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 13.80/14.01            ( ( A ) = ( B ) ) ) ) )),
% 13.80/14.01    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 13.80/14.01  thf('27', plain,
% 13.80/14.01      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 13.80/14.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.80/14.01  thf('28', plain,
% 13.80/14.01      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.80/14.01         ((r2_hidden @ X29 @ X30)
% 13.80/14.01          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 13.80/14.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 13.80/14.01  thf('29', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i]:
% 13.80/14.01         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 13.80/14.01          | (r2_hidden @ X1 @ sk_B))),
% 13.80/14.01      inference('sup-', [status(thm)], ['27', '28'])).
% 13.80/14.01  thf('30', plain,
% 13.80/14.01      (![X0 : $i]:
% 13.80/14.01         (((sk_B) = (k1_xboole_0))
% 13.80/14.01          | (r1_tarski @ sk_A @ X0)
% 13.80/14.01          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 13.80/14.01      inference('sup-', [status(thm)], ['26', '29'])).
% 13.80/14.01  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 13.80/14.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.80/14.01  thf('32', plain,
% 13.80/14.01      (![X0 : $i]:
% 13.80/14.01         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 13.80/14.01      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 13.80/14.01  thf('33', plain,
% 13.80/14.01      (![X1 : $i, X3 : $i]:
% 13.80/14.01         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 13.80/14.01      inference('cnf', [status(esa)], [d3_tarski])).
% 13.80/14.01  thf('34', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 13.80/14.01      inference('sup-', [status(thm)], ['32', '33'])).
% 13.80/14.01  thf('35', plain, ((r1_tarski @ sk_A @ sk_B)),
% 13.80/14.01      inference('simplify', [status(thm)], ['34'])).
% 13.80/14.01  thf(d8_xboole_0, axiom,
% 13.80/14.01    (![A:$i,B:$i]:
% 13.80/14.01     ( ( r2_xboole_0 @ A @ B ) <=>
% 13.80/14.01       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 13.80/14.01  thf('36', plain,
% 13.80/14.01      (![X4 : $i, X6 : $i]:
% 13.80/14.01         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 13.80/14.01      inference('cnf', [status(esa)], [d8_xboole_0])).
% 13.80/14.01  thf('37', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 13.80/14.01      inference('sup-', [status(thm)], ['35', '36'])).
% 13.80/14.01  thf('38', plain, (((sk_A) != (sk_B))),
% 13.80/14.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.80/14.01  thf('39', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 13.80/14.01      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 13.80/14.01  thf(t6_xboole_0, axiom,
% 13.80/14.01    (![A:$i,B:$i]:
% 13.80/14.01     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 13.80/14.01          ( ![C:$i]:
% 13.80/14.01            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 13.80/14.01  thf('40', plain,
% 13.80/14.01      (![X11 : $i, X12 : $i]:
% 13.80/14.01         (~ (r2_xboole_0 @ X11 @ X12)
% 13.80/14.01          | (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X12))),
% 13.80/14.01      inference('cnf', [status(esa)], [t6_xboole_0])).
% 13.80/14.01  thf('41', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_B)),
% 13.80/14.01      inference('sup-', [status(thm)], ['39', '40'])).
% 13.80/14.01  thf('42', plain,
% 13.80/14.01      (![X1 : $i, X3 : $i]:
% 13.80/14.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 13.80/14.01      inference('cnf', [status(esa)], [d3_tarski])).
% 13.80/14.01  thf('43', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 13.80/14.01      inference('demod', [status(thm)], ['18', '19'])).
% 13.80/14.01  thf('44', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 13.80/14.01      inference('sup-', [status(thm)], ['42', '43'])).
% 13.80/14.01  thf('45', plain,
% 13.80/14.01      (![X4 : $i, X6 : $i]:
% 13.80/14.01         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 13.80/14.01      inference('cnf', [status(esa)], [d8_xboole_0])).
% 13.80/14.01  thf('46', plain,
% 13.80/14.01      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 13.80/14.01      inference('sup-', [status(thm)], ['44', '45'])).
% 13.80/14.01  thf('47', plain,
% 13.80/14.01      (![X11 : $i, X12 : $i]:
% 13.80/14.01         (~ (r2_xboole_0 @ X11 @ X12)
% 13.80/14.01          | (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X12))),
% 13.80/14.01      inference('cnf', [status(esa)], [t6_xboole_0])).
% 13.80/14.01  thf('48', plain,
% 13.80/14.01      (![X0 : $i]:
% 13.80/14.01         (((k1_xboole_0) = (X0))
% 13.80/14.01          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 13.80/14.01      inference('sup-', [status(thm)], ['46', '47'])).
% 13.80/14.01  thf('49', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.80/14.01         (((X0) = (k1_xboole_0))
% 13.80/14.01          | ~ (r2_hidden @ X2 @ X1)
% 13.80/14.01          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_3 @ X0 @ k1_xboole_0)) @ 
% 13.80/14.01             (k2_zfmisc_1 @ X1 @ X0)))),
% 13.80/14.01      inference('sup-', [status(thm)], ['23', '24'])).
% 13.80/14.01  thf('50', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i]:
% 13.80/14.01         (((k1_xboole_0) = (X0))
% 13.80/14.01          | (r2_hidden @ 
% 13.80/14.01             (k4_tarski @ (sk_C_2 @ X0 @ k1_xboole_0) @ 
% 13.80/14.01              (sk_C_3 @ X1 @ k1_xboole_0)) @ 
% 13.80/14.01             (k2_zfmisc_1 @ X0 @ X1))
% 13.80/14.01          | ((X1) = (k1_xboole_0)))),
% 13.80/14.01      inference('sup-', [status(thm)], ['48', '49'])).
% 13.80/14.01  thf('51', plain,
% 13.80/14.01      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 13.80/14.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.80/14.01  thf('52', plain,
% 13.80/14.01      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.80/14.01         ((r2_hidden @ X31 @ X32)
% 13.80/14.01          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 13.80/14.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 13.80/14.01  thf('53', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i]:
% 13.80/14.01         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 13.80/14.01          | (r2_hidden @ X0 @ sk_A))),
% 13.80/14.01      inference('sup-', [status(thm)], ['51', '52'])).
% 13.80/14.01  thf('54', plain,
% 13.80/14.01      ((((sk_B) = (k1_xboole_0))
% 13.80/14.01        | ((k1_xboole_0) = (sk_A))
% 13.80/14.01        | (r2_hidden @ (sk_C_3 @ sk_B @ k1_xboole_0) @ sk_A))),
% 13.80/14.01      inference('sup-', [status(thm)], ['50', '53'])).
% 13.80/14.01  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 13.80/14.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.80/14.01  thf('56', plain, (((sk_B) != (k1_xboole_0))),
% 13.80/14.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.80/14.01  thf('57', plain, ((r2_hidden @ (sk_C_3 @ sk_B @ k1_xboole_0) @ sk_A)),
% 13.80/14.01      inference('simplify_reflect-', [status(thm)], ['54', '55', '56'])).
% 13.80/14.01  thf('58', plain,
% 13.80/14.01      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 13.80/14.01         ((r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X33))
% 13.80/14.01          | ~ (r2_hidden @ X31 @ X33)
% 13.80/14.01          | ~ (r2_hidden @ X29 @ X30))),
% 13.80/14.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 13.80/14.01  thf('59', plain,
% 13.80/14.01      (![X0 : $i, X1 : $i]:
% 13.80/14.01         (~ (r2_hidden @ X1 @ X0)
% 13.80/14.01          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_3 @ sk_B @ k1_xboole_0)) @ 
% 13.80/14.01             (k2_zfmisc_1 @ X0 @ sk_A)))),
% 13.80/14.01      inference('sup-', [status(thm)], ['57', '58'])).
% 13.80/14.01  thf('60', plain,
% 13.80/14.01      ((r2_hidden @ 
% 13.80/14.01        (k4_tarski @ (sk_C_2 @ sk_B @ sk_A) @ (sk_C_3 @ sk_B @ k1_xboole_0)) @ 
% 13.80/14.01        (k2_zfmisc_1 @ sk_B @ sk_A))),
% 13.80/14.01      inference('sup-', [status(thm)], ['41', '59'])).
% 13.80/14.01  thf('61', plain,
% 13.80/14.01      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 13.80/14.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.80/14.01  thf('62', plain,
% 13.80/14.01      ((r2_hidden @ 
% 13.80/14.01        (k4_tarski @ (sk_C_2 @ sk_B @ sk_A) @ (sk_C_3 @ sk_B @ k1_xboole_0)) @ 
% 13.80/14.01        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 13.80/14.01      inference('demod', [status(thm)], ['60', '61'])).
% 13.80/14.01  thf('63', plain,
% 13.80/14.01      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.80/14.01         ((r2_hidden @ X29 @ X30)
% 13.80/14.01          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 13.80/14.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 13.80/14.01  thf('64', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)),
% 13.80/14.01      inference('sup-', [status(thm)], ['62', '63'])).
% 13.80/14.01  thf('65', plain,
% 13.80/14.01      (![X11 : $i, X12 : $i]:
% 13.80/14.01         (~ (r2_xboole_0 @ X11 @ X12)
% 13.80/14.01          | ~ (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X11))),
% 13.80/14.01      inference('cnf', [status(esa)], [t6_xboole_0])).
% 13.80/14.01  thf('66', plain, (~ (r2_xboole_0 @ sk_A @ sk_B)),
% 13.80/14.01      inference('sup-', [status(thm)], ['64', '65'])).
% 13.80/14.01  thf('67', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 13.80/14.01      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 13.80/14.01  thf('68', plain, ($false), inference('demod', [status(thm)], ['66', '67'])).
% 13.80/14.01  
% 13.80/14.01  % SZS output end Refutation
% 13.80/14.01  
% 13.80/14.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
