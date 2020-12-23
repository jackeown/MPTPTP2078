%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jxVfwaooZi

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:44 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 176 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   22
%              Number of atoms          :  693 (1490 expanded)
%              Number of equality atoms :   38 (  87 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('1',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ( X25
        = ( k2_zfmisc_1 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X25 @ X21 @ X22 ) @ ( sk_E @ X25 @ X21 @ X22 ) @ ( sk_D @ X25 @ X21 @ X22 ) @ X21 @ X22 )
      | ( r2_hidden @ ( sk_D @ X25 @ X21 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_zfmisc_1 @ X34 @ X35 )
        = k1_xboole_0 )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ X34 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X32 ) )
      | ~ ( r2_hidden @ X30 @ X32 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_D_1 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_C_2 )
      | ( r1_tarski @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_C_2 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['31'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X1 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) @ X1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('46',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ X34 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['31'])).

thf('57',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['32','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['30','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('64',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_zfmisc_1 @ X34 @ X35 )
        = k1_xboole_0 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,(
    ! [X35: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X35 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','64','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jxVfwaooZi
% 0.15/0.37  % Computer   : n015.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:38:08 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 158 iterations in 0.105s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.59  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.38/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.59  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.38/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(t138_zfmisc_1, conjecture,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.59     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.38/0.59       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.59         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.59        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.38/0.59          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.59            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.38/0.59  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(d2_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.59           ( ?[E:$i,F:$i]:
% 0.38/0.59             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.38/0.59               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.38/0.59  thf(zf_stmt_2, axiom,
% 0.38/0.59    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.38/0.59     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.38/0.59       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.38/0.59         ( r2_hidden @ E @ A ) ) ))).
% 0.38/0.59  thf(zf_stmt_3, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.59           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i, X25 : $i]:
% 0.38/0.59         (((X25) = (k2_zfmisc_1 @ X22 @ X21))
% 0.38/0.59          | (zip_tseitin_0 @ (sk_F @ X25 @ X21 @ X22) @ 
% 0.38/0.59             (sk_E @ X25 @ X21 @ X22) @ (sk_D @ X25 @ X21 @ X22) @ X21 @ X22)
% 0.38/0.59          | (r2_hidden @ (sk_D @ X25 @ X21 @ X22) @ X25))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.59         ((r2_hidden @ X13 @ X15)
% 0.38/0.59          | ~ (zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.38/0.59          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.38/0.59          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.59  thf(t3_boole, axiom,
% 0.38/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.59  thf('4', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.59  thf(t48_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X9 : $i, X10 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.38/0.59           = (k3_xboole_0 @ X9 @ X10))),
% 0.38/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.59  thf('7', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.59  thf(t4_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.38/0.59          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.38/0.59          | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.38/0.59  thf('11', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.38/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.59  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.38/0.59          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '12'])).
% 0.38/0.59  thf(t113_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X34 : $i, X35 : $i]:
% 0.38/0.59         (((k2_zfmisc_1 @ X34 @ X35) = (k1_xboole_0))
% 0.38/0.59          | ((X35) != (k1_xboole_0)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X34 : $i]: ((k2_zfmisc_1 @ X34 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((X1) = (k1_xboole_0))
% 0.38/0.59          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.38/0.59      inference('demod', [status(thm)], ['13', '15'])).
% 0.38/0.59  thf(d3_tarski, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf(l54_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.59     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.38/0.59       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i]:
% 0.38/0.59         ((r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X32))
% 0.38/0.59          | ~ (r2_hidden @ X30 @ X32)
% 0.38/0.59          | ~ (r2_hidden @ X28 @ X29))),
% 0.38/0.59      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X0 @ X1)
% 0.38/0.59          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.59          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.38/0.59             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X0 @ X1)
% 0.38/0.59          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.38/0.59             (k2_zfmisc_1 @ X0 @ X2))
% 0.38/0.59          | (r1_tarski @ X2 @ X3))),
% 0.38/0.59      inference('sup-', [status(thm)], ['17', '20'])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.38/0.59        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.59          | (r2_hidden @ X0 @ X2)
% 0.38/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ sk_B @ X0)
% 0.38/0.59          | (r1_tarski @ sk_A @ X1)
% 0.38/0.59          | (r2_hidden @ 
% 0.38/0.59             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.38/0.59             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['21', '24'])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.59         ((r2_hidden @ X30 @ X31)
% 0.38/0.59          | ~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X31)))),
% 0.38/0.59      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ sk_A @ X1)
% 0.38/0.59          | (r1_tarski @ sk_B @ X0)
% 0.38/0.59          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r1_tarski @ sk_B @ sk_D_1)
% 0.38/0.59          | (r1_tarski @ sk_A @ X0)
% 0.38/0.59          | (r1_tarski @ sk_B @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ sk_D_1))),
% 0.38/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.38/0.59      inference('split', [status(esa)], ['31'])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((X1) = (k1_xboole_0))
% 0.38/0.59          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.38/0.59      inference('demod', [status(thm)], ['13', '15'])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ sk_B @ X0)
% 0.38/0.59          | (r1_tarski @ sk_A @ X1)
% 0.38/0.59          | (r2_hidden @ 
% 0.38/0.59             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.38/0.59             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['21', '24'])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.59         ((r2_hidden @ X28 @ X29)
% 0.38/0.59          | ~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X31)))),
% 0.38/0.59      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((r1_tarski @ sk_A @ X1)
% 0.38/0.59          | (r1_tarski @ sk_B @ X0)
% 0.38/0.59          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_C_2))),
% 0.38/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (![X1 : $i, X3 : $i]:
% 0.38/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((r1_tarski @ sk_B @ X0)
% 0.38/0.59          | (r1_tarski @ sk_A @ sk_C_2)
% 0.38/0.59          | (r1_tarski @ sk_A @ sk_C_2))),
% 0.38/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (![X0 : $i]: ((r1_tarski @ sk_A @ sk_C_2) | (r1_tarski @ sk_B @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.38/0.59      inference('split', [status(esa)], ['31'])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 0.38/0.59         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.59          | (r2_hidden @ X0 @ X2)
% 0.38/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      ((![X0 : $i, X1 : $i]:
% 0.38/0.59          ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_B)))
% 0.38/0.59         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      ((![X0 : $i, X1 : $i]:
% 0.38/0.59          (((sk_B) = (k1_xboole_0))
% 0.38/0.59           | (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ X0) @ X1)))
% 0.38/0.59         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['33', '43'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.38/0.59          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.38/0.59          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.59  thf('48', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.38/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['44', '49'])).
% 0.38/0.59  thf('51', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.59         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      (![X34 : $i]: ((k2_zfmisc_1 @ X34 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.59  thf('54', plain,
% 0.38/0.59      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.38/0.59      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.59  thf('55', plain, (((r1_tarski @ sk_A @ sk_C_2))),
% 0.38/0.59      inference('simplify', [status(thm)], ['54'])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      (~ ((r1_tarski @ sk_B @ sk_D_1)) | ~ ((r1_tarski @ sk_A @ sk_C_2))),
% 0.38/0.59      inference('split', [status(esa)], ['31'])).
% 0.38/0.59  thf('57', plain, (~ ((r1_tarski @ sk_B @ sk_D_1))),
% 0.38/0.59      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.38/0.59  thf('58', plain, (~ (r1_tarski @ sk_B @ sk_D_1)),
% 0.38/0.59      inference('simpl_trail', [status(thm)], ['32', '57'])).
% 0.38/0.59  thf('59', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.38/0.59      inference('clc', [status(thm)], ['30', '58'])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.59          | (r2_hidden @ X0 @ X2)
% 0.38/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('61', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((sk_A) = (k1_xboole_0))
% 0.38/0.59          | (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['16', '61'])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('64', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.59  thf('65', plain,
% 0.38/0.59      (![X34 : $i, X35 : $i]:
% 0.38/0.59         (((k2_zfmisc_1 @ X34 @ X35) = (k1_xboole_0))
% 0.38/0.59          | ((X34) != (k1_xboole_0)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.59  thf('66', plain,
% 0.38/0.59      (![X35 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X35) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.38/0.59  thf('67', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['0', '64', '66'])).
% 0.38/0.59  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
