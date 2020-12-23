%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xyv8KiKybx

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:01 EST 2020

% Result     : Theorem 5.82s
% Output     : Refutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :  196 (3178 expanded)
%              Number of leaves         :   27 ( 957 expanded)
%              Depth                    :   38
%              Number of atoms          : 1897 (37434 expanded)
%              Number of equality atoms :  232 (2797 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

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

thf('5',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( X23
        = ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X23 @ X19 @ X20 ) @ ( sk_E @ X23 @ X19 @ X20 ) @ ( sk_D @ X23 @ X19 @ X20 ) @ X19 @ X20 )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X13 )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X31: $i] :
      ( ( X31
        = ( k3_tarski @ X27 ) )
      | ( r2_hidden @ ( sk_D_1 @ X31 @ X27 ) @ X27 )
      | ( r2_hidden @ ( sk_C_2 @ X31 @ X27 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('10',plain,(
    ! [X27: $i,X31: $i] :
      ( ( X31
        = ( k3_tarski @ X27 ) )
      | ( r2_hidden @ ( sk_D_1 @ X31 @ X27 ) @ X27 )
      | ( r2_hidden @ ( sk_C_2 @ X31 @ X27 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

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

thf('11',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X27: $i,X31: $i,X32: $i] :
      ( ( X31
        = ( k3_tarski @ X27 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X31 @ X27 ) @ X32 )
      | ~ ( r2_hidden @ X32 @ X27 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X31 @ X27 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('24',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( k1_xboole_0
    = ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','29'])).

thf('32',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( sk_D @ k1_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( sk_D @ k1_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['4','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('41',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['42','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k2_zfmisc_1 @ X0 @ sk_B ) )
        | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k2_zfmisc_1 @ X0 @ sk_B ) )
        | ( r2_hidden @ sk_B @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('65',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( k1_xboole_0
          = ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( sk_B
          = ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['62','72'])).

thf('74',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('78',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('81',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('83',plain,
    ( k1_xboole_0
    = ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('87',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X15 )
      | ~ ( r2_hidden @ X10 @ X15 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ( X12
       != ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,(
    ! [X10: $i,X11: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X10 @ X15 )
      | ( zip_tseitin_0 @ X11 @ X10 @ ( k4_tarski @ X10 @ X11 ) @ X13 @ X15 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_C @ X2 @ X1 ) @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( k4_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ X1 @ X0 )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ X0 @ sk_B ) ) @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('97',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
        | ( r1_tarski @ sk_B @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_B @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r2_hidden @ X1 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( r2_hidden @ ( sk_C_2 @ sk_B @ k1_xboole_0 ) @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','105'])).

thf('107',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('109',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','108'])).

thf('110',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['107','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_2 @ sk_B @ k1_xboole_0 ) @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['106','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('113',plain,
    ( k1_xboole_0
    = ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['107','109'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','117'])).

thf('119',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('120',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('123',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('124',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('125',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( X23
        = ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X23 @ X19 @ X20 ) @ ( sk_E @ X23 @ X19 @ X20 ) @ ( sk_D @ X23 @ X19 @ X20 ) @ X19 @ X20 )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('126',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X10 @ X14 )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','28'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('131',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('140',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k2_zfmisc_1 @ sk_A @ X0 ) )
        | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['123','145'])).

thf('147',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('148',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('149',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k2_zfmisc_1 @ sk_A @ X0 ) )
        | ( r2_hidden @ sk_A @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('153',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( k1_xboole_0
          = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('159',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('160',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( sk_A
          = ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['150','160'])).

thf('162',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('163',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('165',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','79','80','121','122','166'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xyv8KiKybx
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:25:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.82/6.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.82/6.03  % Solved by: fo/fo7.sh
% 5.82/6.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.82/6.03  % done 4680 iterations in 5.578s
% 5.82/6.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.82/6.03  % SZS output start Refutation
% 5.82/6.03  thf(sk_A_type, type, sk_A: $i).
% 5.82/6.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.82/6.03  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 5.82/6.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.82/6.03  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 5.82/6.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.82/6.03  thf(sk_B_type, type, sk_B: $i).
% 5.82/6.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 5.82/6.03  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 5.82/6.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.82/6.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.82/6.03  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 5.82/6.03  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.82/6.03  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 5.82/6.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.82/6.03  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.82/6.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.82/6.03  thf(t113_zfmisc_1, conjecture,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.82/6.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.82/6.03  thf(zf_stmt_0, negated_conjecture,
% 5.82/6.03    (~( ![A:$i,B:$i]:
% 5.82/6.03        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.82/6.03          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 5.82/6.03    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 5.82/6.03  thf('0', plain,
% 5.82/6.03      ((((sk_B) != (k1_xboole_0))
% 5.82/6.03        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('1', plain,
% 5.82/6.03      (~ (((sk_B) = (k1_xboole_0))) | 
% 5.82/6.03       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('split', [status(esa)], ['0'])).
% 5.82/6.03  thf('2', plain,
% 5.82/6.03      ((((sk_B) = (k1_xboole_0))
% 5.82/6.03        | ((sk_A) = (k1_xboole_0))
% 5.82/6.03        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('3', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 5.82/6.03  thf('4', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 5.82/6.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.82/6.03  thf(d2_zfmisc_1, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i]:
% 5.82/6.03     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 5.82/6.03       ( ![D:$i]:
% 5.82/6.03         ( ( r2_hidden @ D @ C ) <=>
% 5.82/6.03           ( ?[E:$i,F:$i]:
% 5.82/6.03             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 5.82/6.03               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 5.82/6.03  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 5.82/6.03  thf(zf_stmt_2, axiom,
% 5.82/6.03    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 5.82/6.03     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 5.82/6.03       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 5.82/6.03         ( r2_hidden @ E @ A ) ) ))).
% 5.82/6.03  thf(zf_stmt_3, axiom,
% 5.82/6.03    (![A:$i,B:$i,C:$i]:
% 5.82/6.03     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 5.82/6.03       ( ![D:$i]:
% 5.82/6.03         ( ( r2_hidden @ D @ C ) <=>
% 5.82/6.03           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 5.82/6.03  thf('5', plain,
% 5.82/6.03      (![X19 : $i, X20 : $i, X23 : $i]:
% 5.82/6.03         (((X23) = (k2_zfmisc_1 @ X20 @ X19))
% 5.82/6.03          | (zip_tseitin_0 @ (sk_F @ X23 @ X19 @ X20) @ 
% 5.82/6.03             (sk_E @ X23 @ X19 @ X20) @ (sk_D @ X23 @ X19 @ X20) @ X19 @ X20)
% 5.82/6.03          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.82/6.03  thf('6', plain,
% 5.82/6.03      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 5.82/6.03         ((r2_hidden @ X11 @ X13)
% 5.82/6.03          | ~ (zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.82/6.03  thf('7', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 5.82/6.03          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['5', '6'])).
% 5.82/6.03  thf('8', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 5.82/6.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.82/6.03  thf(d4_tarski, axiom,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 5.82/6.03       ( ![C:$i]:
% 5.82/6.03         ( ( r2_hidden @ C @ B ) <=>
% 5.82/6.03           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 5.82/6.03  thf('9', plain,
% 5.82/6.03      (![X27 : $i, X31 : $i]:
% 5.82/6.03         (((X31) = (k3_tarski @ X27))
% 5.82/6.03          | (r2_hidden @ (sk_D_1 @ X31 @ X27) @ X27)
% 5.82/6.03          | (r2_hidden @ (sk_C_2 @ X31 @ X27) @ X31))),
% 5.82/6.03      inference('cnf', [status(esa)], [d4_tarski])).
% 5.82/6.03  thf('10', plain,
% 5.82/6.03      (![X27 : $i, X31 : $i]:
% 5.82/6.03         (((X31) = (k3_tarski @ X27))
% 5.82/6.03          | (r2_hidden @ (sk_D_1 @ X31 @ X27) @ X27)
% 5.82/6.03          | (r2_hidden @ (sk_C_2 @ X31 @ X27) @ X31))),
% 5.82/6.03      inference('cnf', [status(esa)], [d4_tarski])).
% 5.82/6.03  thf(t3_xboole_0, axiom,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 5.82/6.03            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.82/6.03       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.82/6.03            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 5.82/6.03  thf('11', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('12', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 5.82/6.03          | ((X1) = (k3_tarski @ X0))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X2)
% 5.82/6.03          | ~ (r2_hidden @ (sk_D_1 @ X1 @ X0) @ X2))),
% 5.82/6.03      inference('sup-', [status(thm)], ['10', '11'])).
% 5.82/6.03  thf('13', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 5.82/6.03          | ((X1) = (k3_tarski @ X0))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X0)
% 5.82/6.03          | ((X1) = (k3_tarski @ X0))
% 5.82/6.03          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['9', '12'])).
% 5.82/6.03  thf('14', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (~ (r1_xboole_0 @ X0 @ X0)
% 5.82/6.03          | ((X1) = (k3_tarski @ X0))
% 5.82/6.03          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1))),
% 5.82/6.03      inference('simplify', [status(thm)], ['13'])).
% 5.82/6.03  thf('15', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['8', '14'])).
% 5.82/6.03  thf('16', plain,
% 5.82/6.03      (![X27 : $i, X31 : $i, X32 : $i]:
% 5.82/6.03         (((X31) = (k3_tarski @ X27))
% 5.82/6.03          | ~ (r2_hidden @ (sk_C_2 @ X31 @ X27) @ X32)
% 5.82/6.03          | ~ (r2_hidden @ X32 @ X27)
% 5.82/6.03          | ~ (r2_hidden @ (sk_C_2 @ X31 @ X27) @ X31))),
% 5.82/6.03      inference('cnf', [status(esa)], [d4_tarski])).
% 5.82/6.03  thf('17', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((X0) = (k3_tarski @ k1_xboole_0))
% 5.82/6.03          | ~ (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.82/6.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['15', '16'])).
% 5.82/6.03  thf('18', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.82/6.03          | ~ (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['17'])).
% 5.82/6.03  thf('19', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['8', '14'])).
% 5.82/6.03  thf('20', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((X0) = (k3_tarski @ k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 5.82/6.03      inference('clc', [status(thm)], ['18', '19'])).
% 5.82/6.03  thf('21', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 5.82/6.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.82/6.03  thf('22', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['8', '14'])).
% 5.82/6.03  thf('23', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['8', '14'])).
% 5.82/6.03  thf('24', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('25', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((X0) = (k3_tarski @ k1_xboole_0))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X1)
% 5.82/6.03          | ~ (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['23', '24'])).
% 5.82/6.03  thf('26', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((X0) = (k3_tarski @ k1_xboole_0))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X0)
% 5.82/6.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['22', '25'])).
% 5.82/6.03  thf('27', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['26'])).
% 5.82/6.03  thf('28', plain, (((k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['21', '27'])).
% 5.82/6.03  thf('29', plain,
% 5.82/6.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 5.82/6.03      inference('demod', [status(thm)], ['20', '28'])).
% 5.82/6.03  thf('30', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | ((sk_D @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['7', '29'])).
% 5.82/6.03  thf('31', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | ((sk_D @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['7', '29'])).
% 5.82/6.03  thf('32', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('33', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (((sk_D @ k1_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X2)
% 5.82/6.03          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X2))),
% 5.82/6.03      inference('sup-', [status(thm)], ['31', '32'])).
% 5.82/6.03  thf('34', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((sk_D @ k1_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 5.82/6.03          | ((sk_D @ k1_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['30', '33'])).
% 5.82/6.03  thf('35', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (~ (r1_xboole_0 @ X0 @ X0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 5.82/6.03          | ((sk_D @ k1_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['34'])).
% 5.82/6.03  thf('36', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['4', '35'])).
% 5.82/6.03  thf('37', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 5.82/6.03          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['5', '6'])).
% 5.82/6.03  thf('38', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | (r2_hidden @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 5.82/6.03      inference('sup+', [status(thm)], ['36', '37'])).
% 5.82/6.03  thf('39', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['38'])).
% 5.82/6.03  thf('40', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['38'])).
% 5.82/6.03  thf('41', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('42', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 5.82/6.03          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0) @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['40', '41'])).
% 5.82/6.03  thf('43', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 5.82/6.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.82/6.03  thf('44', plain,
% 5.82/6.03      (![X4 : $i, X5 : $i]:
% 5.82/6.03         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.82/6.03  thf('45', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 5.82/6.03      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.82/6.03  thf(d3_tarski, axiom,
% 5.82/6.03    (![A:$i,B:$i]:
% 5.82/6.03     ( ( r1_tarski @ A @ B ) <=>
% 5.82/6.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.82/6.03  thf('46', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X0 @ X1)
% 5.82/6.03          | (r2_hidden @ X0 @ X2)
% 5.82/6.03          | ~ (r1_tarski @ X1 @ X2))),
% 5.82/6.03      inference('cnf', [status(esa)], [d3_tarski])).
% 5.82/6.03  thf('47', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['45', '46'])).
% 5.82/6.03  thf('48', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 5.82/6.03          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['44', '47'])).
% 5.82/6.03  thf('49', plain,
% 5.82/6.03      (![X4 : $i, X5 : $i]:
% 5.82/6.03         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('50', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('51', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((r1_xboole_0 @ X0 @ X1)
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X2)
% 5.82/6.03          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 5.82/6.03      inference('sup-', [status(thm)], ['49', '50'])).
% 5.82/6.03  thf('52', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 5.82/6.03          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 5.82/6.03          | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['48', '51'])).
% 5.82/6.03  thf('53', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 5.82/6.03      inference('simplify', [status(thm)], ['52'])).
% 5.82/6.03  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.82/6.03      inference('sup-', [status(thm)], ['43', '53'])).
% 5.82/6.03  thf('55', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X0) @ X1))),
% 5.82/6.03      inference('demod', [status(thm)], ['42', '54'])).
% 5.82/6.03  thf('56', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['39', '55'])).
% 5.82/6.03  thf('57', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['56'])).
% 5.82/6.03  thf('58', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B))
% 5.82/6.03           | (r2_hidden @ k1_xboole_0 @ k1_xboole_0)))
% 5.82/6.03         <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup+', [status(thm)], ['3', '57'])).
% 5.82/6.03  thf('59', plain,
% 5.82/6.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('60', plain,
% 5.82/6.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('61', plain,
% 5.82/6.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('62', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          (((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)) | (r2_hidden @ sk_B @ sk_B)))
% 5.82/6.03         <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 5.82/6.03  thf('63', plain,
% 5.82/6.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('64', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['56'])).
% 5.82/6.03  thf('65', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('66', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ k1_xboole_0))
% 5.82/6.03          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 5.82/6.03          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['64', '65'])).
% 5.82/6.03  thf('67', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.82/6.03      inference('sup-', [status(thm)], ['43', '53'])).
% 5.82/6.03  thf('68', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ k1_xboole_0))
% 5.82/6.03          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 5.82/6.03      inference('demod', [status(thm)], ['66', '67'])).
% 5.82/6.03  thf('69', plain,
% 5.82/6.03      ((![X0 : $i, X1 : $i]:
% 5.82/6.03          (~ (r2_hidden @ sk_B @ X0)
% 5.82/6.03           | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ k1_xboole_0))))
% 5.82/6.03         <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['63', '68'])).
% 5.82/6.03  thf('70', plain,
% 5.82/6.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('71', plain,
% 5.82/6.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('72', plain,
% 5.82/6.03      ((![X0 : $i, X1 : $i]:
% 5.82/6.03          (~ (r2_hidden @ sk_B @ X0) | ((sk_B) = (k2_zfmisc_1 @ X1 @ sk_B))))
% 5.82/6.03         <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('demod', [status(thm)], ['69', '70', '71'])).
% 5.82/6.03  thf('73', plain,
% 5.82/6.03      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 5.82/6.03         <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('clc', [status(thm)], ['62', '72'])).
% 5.82/6.03  thf('74', plain,
% 5.82/6.03      ((((sk_A) != (k1_xboole_0))
% 5.82/6.03        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.82/6.03  thf('75', plain,
% 5.82/6.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 5.82/6.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['74'])).
% 5.82/6.03  thf('76', plain,
% 5.82/6.03      ((((sk_B) != (k1_xboole_0)))
% 5.82/6.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 5.82/6.03             (((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['73', '75'])).
% 5.82/6.03  thf('77', plain,
% 5.82/6.03      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('78', plain,
% 5.82/6.03      ((((sk_B) != (sk_B)))
% 5.82/6.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 5.82/6.03             (((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('demod', [status(thm)], ['76', '77'])).
% 5.82/6.03  thf('79', plain,
% 5.82/6.03      (~ (((sk_B) = (k1_xboole_0))) | 
% 5.82/6.03       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['78'])).
% 5.82/6.03  thf('80', plain,
% 5.82/6.03      (~ (((sk_A) = (k1_xboole_0))) | 
% 5.82/6.03       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('split', [status(esa)], ['74'])).
% 5.82/6.03  thf('81', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 5.82/6.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.82/6.03  thf('82', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['8', '14'])).
% 5.82/6.03  thf('83', plain, (((k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['21', '27'])).
% 5.82/6.03  thf('84', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ((X0) = (k1_xboole_0)))),
% 5.82/6.03      inference('demod', [status(thm)], ['82', '83'])).
% 5.82/6.03  thf('85', plain,
% 5.82/6.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('86', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 5.82/6.03          | ((X0) = (k1_xboole_0)))),
% 5.82/6.03      inference('demod', [status(thm)], ['82', '83'])).
% 5.82/6.03  thf('87', plain,
% 5.82/6.03      (![X1 : $i, X3 : $i]:
% 5.82/6.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.82/6.03      inference('cnf', [status(esa)], [d3_tarski])).
% 5.82/6.03  thf('88', plain,
% 5.82/6.03      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 5.82/6.03         ((zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X15)
% 5.82/6.03          | ~ (r2_hidden @ X10 @ X15)
% 5.82/6.03          | ~ (r2_hidden @ X11 @ X13)
% 5.82/6.03          | ((X12) != (k4_tarski @ X10 @ X11)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.82/6.03  thf('89', plain,
% 5.82/6.03      (![X10 : $i, X11 : $i, X13 : $i, X15 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X11 @ X13)
% 5.82/6.03          | ~ (r2_hidden @ X10 @ X15)
% 5.82/6.03          | (zip_tseitin_0 @ X11 @ X10 @ (k4_tarski @ X10 @ X11) @ X13 @ X15))),
% 5.82/6.03      inference('simplify', [status(thm)], ['88'])).
% 5.82/6.03  thf('90', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.82/6.03         ((r1_tarski @ X0 @ X1)
% 5.82/6.03          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 5.82/6.03             (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 5.82/6.03          | ~ (r2_hidden @ X3 @ X2))),
% 5.82/6.03      inference('sup-', [status(thm)], ['87', '89'])).
% 5.82/6.03  thf('91', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (((X0) = (k1_xboole_0))
% 5.82/6.03          | (zip_tseitin_0 @ (sk_C @ X2 @ X1) @ (sk_C_2 @ X0 @ k1_xboole_0) @ 
% 5.82/6.03             (k4_tarski @ (sk_C_2 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 5.82/6.03             X1 @ X0)
% 5.82/6.03          | (r1_tarski @ X1 @ X2))),
% 5.82/6.03      inference('sup-', [status(thm)], ['86', '90'])).
% 5.82/6.03  thf('92', plain,
% 5.82/6.03      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 5.82/6.03         (~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20)
% 5.82/6.03          | (r2_hidden @ X18 @ X21)
% 5.82/6.03          | ((X21) != (k2_zfmisc_1 @ X20 @ X19)))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.82/6.03  thf('93', plain,
% 5.82/6.03      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 5.82/6.03         ((r2_hidden @ X18 @ (k2_zfmisc_1 @ X20 @ X19))
% 5.82/6.03          | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 5.82/6.03      inference('simplify', [status(thm)], ['92'])).
% 5.82/6.03  thf('94', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((r1_tarski @ X1 @ X2)
% 5.82/6.03          | ((X0) = (k1_xboole_0))
% 5.82/6.03          | (r2_hidden @ 
% 5.82/6.03             (k4_tarski @ (sk_C_2 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 5.82/6.03             (k2_zfmisc_1 @ X0 @ X1)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['91', '93'])).
% 5.82/6.03  thf('95', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          ((r2_hidden @ 
% 5.82/6.03            (k4_tarski @ (sk_C_2 @ sk_A @ k1_xboole_0) @ (sk_C @ X0 @ sk_B)) @ 
% 5.82/6.03            k1_xboole_0)
% 5.82/6.03           | ((sk_A) = (k1_xboole_0))
% 5.82/6.03           | (r1_tarski @ sk_B @ X0)))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup+', [status(thm)], ['85', '94'])).
% 5.82/6.03  thf('96', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((r1_tarski @ X1 @ X2)
% 5.82/6.03          | ((X0) = (k1_xboole_0))
% 5.82/6.03          | (r2_hidden @ 
% 5.82/6.03             (k4_tarski @ (sk_C_2 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 5.82/6.03             (k2_zfmisc_1 @ X0 @ X1)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['91', '93'])).
% 5.82/6.03  thf('97', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('98', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.82/6.03         (((X1) = (k1_xboole_0))
% 5.82/6.03          | (r1_tarski @ X0 @ X2)
% 5.82/6.03          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X3)
% 5.82/6.03          | ~ (r2_hidden @ 
% 5.82/6.03               (k4_tarski @ (sk_C_2 @ X1 @ k1_xboole_0) @ (sk_C @ X2 @ X0)) @ 
% 5.82/6.03               X3))),
% 5.82/6.03      inference('sup-', [status(thm)], ['96', '97'])).
% 5.82/6.03  thf('99', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          ((r1_tarski @ sk_B @ X0)
% 5.82/6.03           | ((sk_A) = (k1_xboole_0))
% 5.82/6.03           | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 5.82/6.03           | (r1_tarski @ sk_B @ X0)
% 5.82/6.03           | ((sk_A) = (k1_xboole_0))))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['95', '98'])).
% 5.82/6.03  thf('100', plain,
% 5.82/6.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('101', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.82/6.03      inference('sup-', [status(thm)], ['43', '53'])).
% 5.82/6.03  thf('102', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          ((r1_tarski @ sk_B @ X0)
% 5.82/6.03           | ((sk_A) = (k1_xboole_0))
% 5.82/6.03           | (r1_tarski @ sk_B @ X0)
% 5.82/6.03           | ((sk_A) = (k1_xboole_0))))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('demod', [status(thm)], ['99', '100', '101'])).
% 5.82/6.03  thf('103', plain,
% 5.82/6.03      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_B @ X0)))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('simplify', [status(thm)], ['102'])).
% 5.82/6.03  thf('104', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X0 @ X1)
% 5.82/6.03          | (r2_hidden @ X0 @ X2)
% 5.82/6.03          | ~ (r1_tarski @ X1 @ X2))),
% 5.82/6.03      inference('cnf', [status(esa)], [d3_tarski])).
% 5.82/6.03  thf('105', plain,
% 5.82/6.03      ((![X0 : $i, X1 : $i]:
% 5.82/6.03          (((sk_A) = (k1_xboole_0))
% 5.82/6.03           | (r2_hidden @ X1 @ X0)
% 5.82/6.03           | ~ (r2_hidden @ X1 @ sk_B)))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['103', '104'])).
% 5.82/6.03  thf('106', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          (((sk_B) = (k1_xboole_0))
% 5.82/6.03           | (r2_hidden @ (sk_C_2 @ sk_B @ k1_xboole_0) @ X0)
% 5.82/6.03           | ((sk_A) = (k1_xboole_0))))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['84', '105'])).
% 5.82/6.03  thf('107', plain,
% 5.82/6.03      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['0'])).
% 5.82/6.03  thf('108', plain,
% 5.82/6.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 5.82/6.03       ~ (((sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['78'])).
% 5.82/6.03  thf('109', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('sat_resolution*', [status(thm)], ['1', '108'])).
% 5.82/6.03  thf('110', plain, (((sk_B) != (k1_xboole_0))),
% 5.82/6.03      inference('simpl_trail', [status(thm)], ['107', '109'])).
% 5.82/6.03  thf('111', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          ((r2_hidden @ (sk_C_2 @ sk_B @ k1_xboole_0) @ X0)
% 5.82/6.03           | ((sk_A) = (k1_xboole_0))))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('simplify_reflect-', [status(thm)], ['106', '110'])).
% 5.82/6.03  thf('112', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((X0) = (k3_tarski @ k1_xboole_0))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X1)
% 5.82/6.03          | ~ (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['23', '24'])).
% 5.82/6.03  thf('113', plain, (((k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['21', '27'])).
% 5.82/6.03  thf('114', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((X0) = (k1_xboole_0))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X1)
% 5.82/6.03          | ~ (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 5.82/6.03      inference('demod', [status(thm)], ['112', '113'])).
% 5.82/6.03  thf('115', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          (((sk_A) = (k1_xboole_0))
% 5.82/6.03           | ~ (r1_xboole_0 @ sk_B @ X0)
% 5.82/6.03           | ((sk_B) = (k1_xboole_0))))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['111', '114'])).
% 5.82/6.03  thf('116', plain, (((sk_B) != (k1_xboole_0))),
% 5.82/6.03      inference('simpl_trail', [status(thm)], ['107', '109'])).
% 5.82/6.03  thf('117', plain,
% 5.82/6.03      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r1_xboole_0 @ sk_B @ X0)))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('simplify_reflect-', [status(thm)], ['115', '116'])).
% 5.82/6.03  thf('118', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0)))
% 5.82/6.03         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['81', '117'])).
% 5.82/6.03  thf('119', plain,
% 5.82/6.03      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['74'])).
% 5.82/6.03  thf('120', plain,
% 5.82/6.03      ((((sk_A) != (sk_A)))
% 5.82/6.03         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 5.82/6.03             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['118', '119'])).
% 5.82/6.03  thf('121', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) | 
% 5.82/6.03       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['120'])).
% 5.82/6.03  thf('122', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) | 
% 5.82/6.03       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 5.82/6.03       (((sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('123', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('124', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 5.82/6.03      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.82/6.03  thf('125', plain,
% 5.82/6.03      (![X19 : $i, X20 : $i, X23 : $i]:
% 5.82/6.03         (((X23) = (k2_zfmisc_1 @ X20 @ X19))
% 5.82/6.03          | (zip_tseitin_0 @ (sk_F @ X23 @ X19 @ X20) @ 
% 5.82/6.03             (sk_E @ X23 @ X19 @ X20) @ (sk_D @ X23 @ X19 @ X20) @ X19 @ X20)
% 5.82/6.03          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.82/6.03  thf('126', plain,
% 5.82/6.03      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 5.82/6.03         ((r2_hidden @ X10 @ X14)
% 5.82/6.03          | ~ (zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14))),
% 5.82/6.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.82/6.03  thf('127', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 5.82/6.03          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['125', '126'])).
% 5.82/6.03  thf('128', plain,
% 5.82/6.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 5.82/6.03      inference('demod', [status(thm)], ['20', '28'])).
% 5.82/6.03  thf('129', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | ((sk_D @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['127', '128'])).
% 5.82/6.03  thf('130', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | ((sk_D @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['127', '128'])).
% 5.82/6.03  thf('131', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('132', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         (((sk_D @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X2)
% 5.82/6.03          | ~ (r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 5.82/6.03      inference('sup-', [status(thm)], ['130', '131'])).
% 5.82/6.03  thf('133', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((sk_D @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | ~ (r1_xboole_0 @ X0 @ X0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | ((sk_D @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['129', '132'])).
% 5.82/6.03  thf('134', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (~ (r1_xboole_0 @ X0 @ X0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | ((sk_D @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['133'])).
% 5.82/6.03  thf('135', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 5.82/6.03      inference('sup-', [status(thm)], ['124', '134'])).
% 5.82/6.03  thf('136', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 5.82/6.03          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 5.82/6.03          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['125', '126'])).
% 5.82/6.03  thf('137', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | (r2_hidden @ (sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 5.82/6.03      inference('sup+', [status(thm)], ['135', '136'])).
% 5.82/6.03  thf('138', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['137'])).
% 5.82/6.03  thf('139', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['137'])).
% 5.82/6.03  thf('140', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('141', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 5.82/6.03          | ~ (r2_hidden @ (sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 5.82/6.03      inference('sup-', [status(thm)], ['139', '140'])).
% 5.82/6.03  thf('142', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.82/6.03      inference('sup-', [status(thm)], ['43', '53'])).
% 5.82/6.03  thf('143', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | ~ (r2_hidden @ (sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 5.82/6.03      inference('demod', [status(thm)], ['141', '142'])).
% 5.82/6.03  thf('144', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['138', '143'])).
% 5.82/6.03  thf('145', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['144'])).
% 5.82/6.03  thf('146', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          (((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0))
% 5.82/6.03           | (r2_hidden @ k1_xboole_0 @ k1_xboole_0)))
% 5.82/6.03         <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup+', [status(thm)], ['123', '145'])).
% 5.82/6.03  thf('147', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('148', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('149', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('150', plain,
% 5.82/6.03      ((![X0 : $i]:
% 5.82/6.03          (((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)) | (r2_hidden @ sk_A @ sk_A)))
% 5.82/6.03         <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 5.82/6.03  thf('151', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('152', plain,
% 5.82/6.03      (![X0 : $i]:
% 5.82/6.03         (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 5.82/6.03          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 5.82/6.03      inference('simplify', [status(thm)], ['144'])).
% 5.82/6.03  thf('153', plain,
% 5.82/6.03      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.82/6.03         (~ (r2_hidden @ X6 @ X4)
% 5.82/6.03          | ~ (r2_hidden @ X6 @ X7)
% 5.82/6.03          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.82/6.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.82/6.03  thf('154', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))
% 5.82/6.03          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 5.82/6.03          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 5.82/6.03      inference('sup-', [status(thm)], ['152', '153'])).
% 5.82/6.03  thf('155', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.82/6.03      inference('sup-', [status(thm)], ['43', '53'])).
% 5.82/6.03  thf('156', plain,
% 5.82/6.03      (![X0 : $i, X1 : $i]:
% 5.82/6.03         (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))
% 5.82/6.03          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 5.82/6.03      inference('demod', [status(thm)], ['154', '155'])).
% 5.82/6.03  thf('157', plain,
% 5.82/6.03      ((![X0 : $i, X1 : $i]:
% 5.82/6.03          (~ (r2_hidden @ sk_A @ X0)
% 5.82/6.03           | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))))
% 5.82/6.03         <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['151', '156'])).
% 5.82/6.03  thf('158', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('159', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('160', plain,
% 5.82/6.03      ((![X0 : $i, X1 : $i]:
% 5.82/6.03          (~ (r2_hidden @ sk_A @ X0) | ((sk_A) = (k2_zfmisc_1 @ sk_A @ X1))))
% 5.82/6.03         <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('demod', [status(thm)], ['157', '158', '159'])).
% 5.82/6.03  thf('161', plain,
% 5.82/6.03      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 5.82/6.03         <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('clc', [status(thm)], ['150', '160'])).
% 5.82/6.03  thf('162', plain,
% 5.82/6.03      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 5.82/6.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['74'])).
% 5.82/6.03  thf('163', plain,
% 5.82/6.03      ((((sk_A) != (k1_xboole_0)))
% 5.82/6.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 5.82/6.03             (((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('sup-', [status(thm)], ['161', '162'])).
% 5.82/6.03  thf('164', plain,
% 5.82/6.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('split', [status(esa)], ['2'])).
% 5.82/6.03  thf('165', plain,
% 5.82/6.03      ((((sk_A) != (sk_A)))
% 5.82/6.03         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 5.82/6.03             (((sk_A) = (k1_xboole_0))))),
% 5.82/6.03      inference('demod', [status(thm)], ['163', '164'])).
% 5.82/6.03  thf('166', plain,
% 5.82/6.03      (~ (((sk_A) = (k1_xboole_0))) | 
% 5.82/6.03       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.82/6.03      inference('simplify', [status(thm)], ['165'])).
% 5.82/6.03  thf('167', plain, ($false),
% 5.82/6.03      inference('sat_resolution*', [status(thm)],
% 5.82/6.03                ['1', '79', '80', '121', '122', '166'])).
% 5.82/6.03  
% 5.82/6.03  % SZS output end Refutation
% 5.82/6.03  
% 5.82/6.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
