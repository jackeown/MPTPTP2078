%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8gmU0XOMwB

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:45 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 154 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  685 (1275 expanded)
%              Number of equality atoms :   43 (  79 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i,X36: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ X36 ) )
      | ~ ( r2_hidden @ X34 @ X36 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D_1 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i,X36: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ X36 ) )
      | ~ ( r2_hidden @ X34 @ X36 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_2 )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['15'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( X29
        = ( k2_zfmisc_1 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X29 @ X25 @ X26 ) @ ( sk_E @ X29 @ X25 @ X26 ) @ ( sk_D @ X29 @ X25 @ X26 ) @ X25 @ X26 )
      | ( r2_hidden @ ( sk_D @ X29 @ X25 @ X26 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X19 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','42'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['32','46'])).

thf('48',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
    | ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['15'])).

thf('50',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['16','50'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['14','51'])).

thf('53',plain,(
    ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','52'])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( X29
        = ( k2_zfmisc_1 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X29 @ X25 @ X26 ) @ ( sk_E @ X29 @ X25 @ X26 ) @ ( sk_D @ X29 @ X25 @ X26 ) @ X25 @ X26 )
      | ( r2_hidden @ ( sk_D @ X29 @ X25 @ X26 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X16 @ X20 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','42'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','42'])).

thf('60',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['53','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8gmU0XOMwB
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.52/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.76  % Solved by: fo/fo7.sh
% 0.52/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.76  % done 319 iterations in 0.301s
% 0.52/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.76  % SZS output start Refutation
% 0.52/0.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.52/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.52/0.76  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.76  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.76  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.52/0.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.76  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.52/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.76  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.52/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.76  thf(t138_zfmisc_1, conjecture,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.52/0.76       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.76         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.52/0.76          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.76            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.52/0.76    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.52/0.76  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t7_xboole_0, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.76          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.52/0.76  thf('1', plain,
% 0.52/0.76      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.52/0.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.52/0.76  thf(d3_tarski, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.76  thf('2', plain,
% 0.52/0.76      (![X1 : $i, X3 : $i]:
% 0.52/0.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.76  thf(l54_zfmisc_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.52/0.76       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.52/0.76  thf('3', plain,
% 0.52/0.76      (![X32 : $i, X33 : $i, X34 : $i, X36 : $i]:
% 0.52/0.76         ((r2_hidden @ (k4_tarski @ X32 @ X34) @ (k2_zfmisc_1 @ X33 @ X36))
% 0.52/0.76          | ~ (r2_hidden @ X34 @ X36)
% 0.52/0.76          | ~ (r2_hidden @ X32 @ X33))),
% 0.52/0.76      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.76  thf('4', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         ((r1_tarski @ X0 @ X1)
% 0.52/0.76          | ~ (r2_hidden @ X3 @ X2)
% 0.52/0.76          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.52/0.76             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.76  thf('5', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (((X0) = (k1_xboole_0))
% 0.52/0.76          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.52/0.76             (k2_zfmisc_1 @ X0 @ X1))
% 0.52/0.76          | (r1_tarski @ X1 @ X2))),
% 0.52/0.76      inference('sup-', [status(thm)], ['1', '4'])).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.52/0.76        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('7', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.76          | (r2_hidden @ X0 @ X2)
% 0.52/0.76          | ~ (r1_tarski @ X1 @ X2))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.76  thf('8', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.52/0.76          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.76  thf('9', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r1_tarski @ sk_B_1 @ X0)
% 0.52/0.76          | ((sk_A) = (k1_xboole_0))
% 0.52/0.76          | (r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.52/0.76             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['5', '8'])).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.76         ((r2_hidden @ X34 @ X35)
% 0.52/0.76          | ~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ (k2_zfmisc_1 @ X33 @ X35)))),
% 0.52/0.76      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.76  thf('11', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((sk_A) = (k1_xboole_0))
% 0.52/0.76          | (r1_tarski @ sk_B_1 @ X0)
% 0.52/0.76          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_D_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.76  thf('12', plain,
% 0.52/0.76      (![X1 : $i, X3 : $i]:
% 0.52/0.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.76  thf('13', plain,
% 0.52/0.76      (((r1_tarski @ sk_B_1 @ sk_D_1)
% 0.52/0.76        | ((sk_A) = (k1_xboole_0))
% 0.52/0.76        | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.76  thf('14', plain,
% 0.52/0.76      ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.52/0.76      inference('simplify', [status(thm)], ['13'])).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('16', plain,
% 0.52/0.76      ((~ (r1_tarski @ sk_B_1 @ sk_D_1)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 0.52/0.76      inference('split', [status(esa)], ['15'])).
% 0.52/0.76  thf('17', plain,
% 0.52/0.76      (![X1 : $i, X3 : $i]:
% 0.52/0.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.52/0.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.52/0.76  thf('19', plain,
% 0.52/0.76      (![X32 : $i, X33 : $i, X34 : $i, X36 : $i]:
% 0.52/0.76         ((r2_hidden @ (k4_tarski @ X32 @ X34) @ (k2_zfmisc_1 @ X33 @ X36))
% 0.52/0.76          | ~ (r2_hidden @ X34 @ X36)
% 0.52/0.76          | ~ (r2_hidden @ X32 @ X33))),
% 0.52/0.76      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.76  thf('20', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (((X0) = (k1_xboole_0))
% 0.52/0.76          | ~ (r2_hidden @ X2 @ X1)
% 0.52/0.76          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.52/0.76             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.76  thf('21', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         ((r1_tarski @ X0 @ X1)
% 0.52/0.76          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.52/0.76             (k2_zfmisc_1 @ X0 @ X2))
% 0.52/0.76          | ((X2) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['17', '20'])).
% 0.52/0.76  thf('22', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.52/0.76          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.76  thf('23', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((sk_B_1) = (k1_xboole_0))
% 0.52/0.76          | (r1_tarski @ sk_A @ X0)
% 0.52/0.76          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.52/0.76             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('24', plain,
% 0.52/0.76      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.76         ((r2_hidden @ X32 @ X33)
% 0.52/0.76          | ~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ (k2_zfmisc_1 @ X33 @ X35)))),
% 0.52/0.76      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.52/0.76  thf('25', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r1_tarski @ sk_A @ X0)
% 0.52/0.76          | ((sk_B_1) = (k1_xboole_0))
% 0.52/0.76          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_2))),
% 0.52/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.76  thf('26', plain,
% 0.52/0.76      (![X1 : $i, X3 : $i]:
% 0.52/0.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.76  thf('27', plain,
% 0.52/0.76      ((((sk_B_1) = (k1_xboole_0))
% 0.52/0.76        | (r1_tarski @ sk_A @ sk_C_2)
% 0.52/0.76        | (r1_tarski @ sk_A @ sk_C_2))),
% 0.52/0.76      inference('sup-', [status(thm)], ['25', '26'])).
% 0.52/0.76  thf('28', plain,
% 0.52/0.76      (((r1_tarski @ sk_A @ sk_C_2) | ((sk_B_1) = (k1_xboole_0)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['27'])).
% 0.52/0.76  thf('29', plain,
% 0.52/0.76      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.52/0.76      inference('split', [status(esa)], ['15'])).
% 0.52/0.76  thf('30', plain,
% 0.52/0.76      ((((sk_B_1) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.76  thf('31', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('32', plain,
% 0.52/0.76      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.76         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.76  thf(d2_zfmisc_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.52/0.76       ( ![D:$i]:
% 0.52/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.76           ( ?[E:$i,F:$i]:
% 0.52/0.76             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.52/0.76               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.52/0.76  thf(zf_stmt_2, axiom,
% 0.52/0.76    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.52/0.76     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.52/0.76       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.52/0.76         ( r2_hidden @ E @ A ) ) ))).
% 0.52/0.76  thf(zf_stmt_3, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.52/0.76       ( ![D:$i]:
% 0.52/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.76           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.52/0.76  thf('33', plain,
% 0.52/0.76      (![X25 : $i, X26 : $i, X29 : $i]:
% 0.52/0.76         (((X29) = (k2_zfmisc_1 @ X26 @ X25))
% 0.52/0.76          | (zip_tseitin_0 @ (sk_F @ X29 @ X25 @ X26) @ 
% 0.52/0.76             (sk_E @ X29 @ X25 @ X26) @ (sk_D @ X29 @ X25 @ X26) @ X25 @ X26)
% 0.52/0.76          | (r2_hidden @ (sk_D @ X29 @ X25 @ X26) @ X29))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.76  thf('34', plain,
% 0.52/0.76      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.76         ((r2_hidden @ X17 @ X19)
% 0.52/0.76          | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 @ X20))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.76  thf('35', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.52/0.76          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.52/0.76          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.76  thf(t2_boole, axiom,
% 0.52/0.76    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.76  thf('36', plain,
% 0.52/0.76      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.76  thf(t4_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.76            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.76       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.52/0.76            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.52/0.76  thf('37', plain,
% 0.52/0.76      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.52/0.76          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.52/0.76      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.52/0.76  thf('38', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.76  thf(t3_boole, axiom,
% 0.52/0.76    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.76  thf('39', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.52/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.76  thf(t83_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.76  thf('40', plain,
% 0.52/0.76      (![X13 : $i, X15 : $i]:
% 0.52/0.76         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.52/0.76  thf('41', plain,
% 0.52/0.76      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.76  thf('42', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.52/0.76      inference('simplify', [status(thm)], ['41'])).
% 0.52/0.76  thf('43', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.52/0.76      inference('demod', [status(thm)], ['38', '42'])).
% 0.52/0.76  thf('44', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.52/0.76          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['35', '43'])).
% 0.52/0.76  thf('45', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.52/0.76      inference('demod', [status(thm)], ['38', '42'])).
% 0.52/0.76  thf('46', plain,
% 0.52/0.76      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.76  thf('47', plain,
% 0.52/0.76      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.52/0.76      inference('demod', [status(thm)], ['32', '46'])).
% 0.52/0.76  thf('48', plain, (((r1_tarski @ sk_A @ sk_C_2))),
% 0.52/0.76      inference('simplify', [status(thm)], ['47'])).
% 0.52/0.76  thf('49', plain,
% 0.52/0.76      (~ ((r1_tarski @ sk_B_1 @ sk_D_1)) | ~ ((r1_tarski @ sk_A @ sk_C_2))),
% 0.52/0.76      inference('split', [status(esa)], ['15'])).
% 0.52/0.76  thf('50', plain, (~ ((r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.52/0.76  thf('51', plain, (~ (r1_tarski @ sk_B_1 @ sk_D_1)),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['16', '50'])).
% 0.52/0.76  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.76      inference('clc', [status(thm)], ['14', '51'])).
% 0.52/0.76  thf('53', plain, (((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.52/0.76      inference('demod', [status(thm)], ['0', '52'])).
% 0.52/0.76  thf('54', plain,
% 0.52/0.76      (![X25 : $i, X26 : $i, X29 : $i]:
% 0.52/0.76         (((X29) = (k2_zfmisc_1 @ X26 @ X25))
% 0.52/0.76          | (zip_tseitin_0 @ (sk_F @ X29 @ X25 @ X26) @ 
% 0.52/0.76             (sk_E @ X29 @ X25 @ X26) @ (sk_D @ X29 @ X25 @ X26) @ X25 @ X26)
% 0.52/0.76          | (r2_hidden @ (sk_D @ X29 @ X25 @ X26) @ X29))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.76  thf('55', plain,
% 0.52/0.76      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.76         ((r2_hidden @ X16 @ X20)
% 0.52/0.76          | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 @ X20))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.76  thf('56', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.52/0.76          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.52/0.76          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.76  thf('57', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.52/0.76      inference('demod', [status(thm)], ['38', '42'])).
% 0.52/0.76  thf('58', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.52/0.76          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.76  thf('59', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.52/0.76      inference('demod', [status(thm)], ['38', '42'])).
% 0.52/0.76  thf('60', plain,
% 0.52/0.76      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.76  thf('61', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.76      inference('demod', [status(thm)], ['53', '60'])).
% 0.52/0.76  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.52/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
