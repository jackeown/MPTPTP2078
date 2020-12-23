%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iw3Nc5yvP1

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:04 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 308 expanded)
%              Number of leaves         :   23 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          : 1230 (3367 expanded)
%              Number of equality atoms :  154 ( 348 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

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

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k4_xboole_0 @ X7 @ X9 )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( sk_B != sk_B )
        | ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('19',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k4_xboole_0 @ X7 @ X9 )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( X23
        = ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X23 @ X19 @ X20 ) @ ( sk_E @ X23 @ X19 @ X20 ) @ ( sk_D @ X23 @ X19 @ X20 ) @ X19 @ X20 )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X13 )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('34',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('45',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('48',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X30 ) )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ k1_xboole_0 )
        | ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_A @ X1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ k1_xboole_0 )
        | ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_A @ X1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('56',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('57',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( r1_xboole_0 @ sk_A @ X1 )
        | ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ k1_xboole_0 @ X2 )
        | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ X2 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( r1_xboole_0 @ sk_A @ X1 )
        | ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ X2 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_A @ X1 )
        | ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_A @ X1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_A @ X1 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('62',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_A @ X0 )
        | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('65',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('70',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('73',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k4_xboole_0 @ X7 @ X9 )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( sk_A != sk_A )
        | ( r1_xboole_0 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_A @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('83',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( X23
        = ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X23 @ X19 @ X20 ) @ ( sk_E @ X23 @ X19 @ X20 ) @ ( sk_D @ X23 @ X19 @ X20 ) @ X19 @ X20 )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X10 @ X14 )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('87',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('93',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','96'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('101',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('103',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('106',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','71','104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iw3Nc5yvP1
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:57:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.49/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.67  % Solved by: fo/fo7.sh
% 0.49/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.67  % done 349 iterations in 0.226s
% 0.49/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.67  % SZS output start Refutation
% 0.49/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.49/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.67  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.49/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.67  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.49/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.67  thf(t113_zfmisc_1, conjecture,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.49/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.67    (~( ![A:$i,B:$i]:
% 0.49/0.67        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.49/0.67          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.49/0.67    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.49/0.67  thf('0', plain,
% 0.49/0.67      ((((sk_B) != (k1_xboole_0))
% 0.49/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('1', plain,
% 0.49/0.67      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.49/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.67      inference('split', [status(esa)], ['0'])).
% 0.49/0.67  thf('2', plain,
% 0.49/0.67      ((((sk_B) = (k1_xboole_0))
% 0.49/0.67        | ((sk_A) = (k1_xboole_0))
% 0.49/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('3', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf(t4_boole, axiom,
% 0.49/0.67    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.49/0.67  thf('4', plain,
% 0.49/0.67      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [t4_boole])).
% 0.49/0.67  thf('5', plain,
% 0.49/0.67      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))
% 0.49/0.67         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['3', '4'])).
% 0.49/0.67  thf('6', plain, ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('7', plain,
% 0.49/0.67      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))
% 0.49/0.67         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('demod', [status(thm)], ['5', '6'])).
% 0.49/0.67  thf(t83_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.49/0.67  thf('8', plain,
% 0.49/0.67      (![X7 : $i, X9 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X7 @ X9) | ((k4_xboole_0 @ X7 @ X9) != (X7)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.49/0.67  thf('9', plain,
% 0.49/0.67      ((![X0 : $i]: (((sk_B) != (sk_B)) | (r1_xboole_0 @ sk_B @ X0)))
% 0.49/0.67         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.67  thf('10', plain,
% 0.49/0.67      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['9'])).
% 0.49/0.67  thf(t3_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.49/0.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.67            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.49/0.67  thf('11', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('12', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('13', plain,
% 0.49/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.49/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('14', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X1 @ X0)
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.49/0.67          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.49/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.67  thf('15', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X0 @ X1)
% 0.49/0.67          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.49/0.67          | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('sup-', [status(thm)], ['11', '14'])).
% 0.49/0.67  thf('16', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('simplify', [status(thm)], ['15'])).
% 0.49/0.67  thf('17', plain,
% 0.49/0.67      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['10', '16'])).
% 0.49/0.67  thf('18', plain,
% 0.49/0.67      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [t4_boole])).
% 0.49/0.67  thf('19', plain,
% 0.49/0.67      (![X7 : $i, X9 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X7 @ X9) | ((k4_xboole_0 @ X7 @ X9) != (X7)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.49/0.67  thf('20', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.49/0.67  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.49/0.67      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.67  thf('22', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('simplify', [status(thm)], ['15'])).
% 0.49/0.67  thf('23', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.49/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.67  thf(d2_zfmisc_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.49/0.67       ( ![D:$i]:
% 0.49/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.67           ( ?[E:$i,F:$i]:
% 0.49/0.67             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.49/0.67               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.49/0.67  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.49/0.67  thf(zf_stmt_2, axiom,
% 0.49/0.67    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.49/0.67     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.49/0.67       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.49/0.67         ( r2_hidden @ E @ A ) ) ))).
% 0.49/0.67  thf(zf_stmt_3, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.49/0.67       ( ![D:$i]:
% 0.49/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.67           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.49/0.67  thf('24', plain,
% 0.49/0.67      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.49/0.67         (((X23) = (k2_zfmisc_1 @ X20 @ X19))
% 0.49/0.67          | (zip_tseitin_0 @ (sk_F @ X23 @ X19 @ X20) @ 
% 0.49/0.67             (sk_E @ X23 @ X19 @ X20) @ (sk_D @ X23 @ X19 @ X20) @ X19 @ X20)
% 0.49/0.67          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('25', plain,
% 0.49/0.67      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.49/0.67         ((r2_hidden @ X11 @ X13)
% 0.49/0.67          | ~ (zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.67  thf('26', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.67          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.49/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.49/0.67  thf('27', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.67          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.49/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.49/0.67  thf('28', plain,
% 0.49/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.49/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('29', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.49/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.49/0.67          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.49/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.49/0.67  thf('30', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.49/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.67          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.49/0.67      inference('sup-', [status(thm)], ['26', '29'])).
% 0.49/0.67  thf('31', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         (~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.67          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.49/0.67      inference('simplify', [status(thm)], ['30'])).
% 0.49/0.67  thf('32', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.49/0.67          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['23', '31'])).
% 0.49/0.67  thf('33', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.49/0.67          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['23', '31'])).
% 0.49/0.67  thf('34', plain,
% 0.49/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.49/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('35', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.49/0.67          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X2))),
% 0.49/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.67  thf('36', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.67          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['32', '35'])).
% 0.49/0.67  thf('37', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['36'])).
% 0.49/0.67  thf('38', plain,
% 0.49/0.67      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.67         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['17', '37'])).
% 0.49/0.67  thf('39', plain,
% 0.49/0.67      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('40', plain,
% 0.49/0.67      ((![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.67         <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('demod', [status(thm)], ['38', '39'])).
% 0.49/0.67  thf('41', plain,
% 0.49/0.67      ((((sk_A) != (k1_xboole_0))
% 0.49/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('42', plain,
% 0.49/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.49/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['41'])).
% 0.49/0.67  thf('43', plain,
% 0.49/0.67      ((((sk_B) != (k1_xboole_0)))
% 0.49/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.67             (((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['40', '42'])).
% 0.49/0.67  thf('44', plain,
% 0.49/0.67      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('45', plain,
% 0.49/0.67      ((((sk_B) != (sk_B)))
% 0.49/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.67             (((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('demod', [status(thm)], ['43', '44'])).
% 0.49/0.67  thf('46', plain,
% 0.49/0.67      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.49/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['45'])).
% 0.49/0.67  thf('47', plain,
% 0.49/0.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.49/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.67      inference('split', [status(esa)], ['41'])).
% 0.49/0.67  thf('48', plain,
% 0.49/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('49', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('50', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf(l54_zfmisc_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.67     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.49/0.67       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.49/0.67  thf('51', plain,
% 0.49/0.67      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.49/0.67         ((r2_hidden @ (k4_tarski @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X30))
% 0.49/0.67          | ~ (r2_hidden @ X28 @ X30)
% 0.49/0.67          | ~ (r2_hidden @ X26 @ X27))),
% 0.49/0.67      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.49/0.67  thf('52', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X0 @ X1)
% 0.49/0.67          | ~ (r2_hidden @ X3 @ X2)
% 0.49/0.67          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.49/0.67             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.49/0.67  thf('53', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X0 @ X1)
% 0.49/0.67          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.49/0.67             (k2_zfmisc_1 @ X0 @ X2))
% 0.49/0.67          | (r1_xboole_0 @ X2 @ X3))),
% 0.49/0.67      inference('sup-', [status(thm)], ['49', '52'])).
% 0.49/0.67  thf('54', plain,
% 0.49/0.67      ((![X0 : $i, X1 : $i]:
% 0.49/0.67          ((r2_hidden @ 
% 0.49/0.67            (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ k1_xboole_0)
% 0.49/0.67           | (r1_xboole_0 @ sk_B @ X0)
% 0.49/0.67           | (r1_xboole_0 @ sk_A @ X1)))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['48', '53'])).
% 0.49/0.67  thf('55', plain,
% 0.49/0.67      ((![X0 : $i, X1 : $i]:
% 0.49/0.67          ((r2_hidden @ 
% 0.49/0.67            (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ k1_xboole_0)
% 0.49/0.67           | (r1_xboole_0 @ sk_B @ X0)
% 0.49/0.67           | (r1_xboole_0 @ sk_A @ X1)))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['48', '53'])).
% 0.49/0.67  thf('56', plain,
% 0.49/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.49/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('57', plain,
% 0.49/0.67      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67          ((r1_xboole_0 @ sk_A @ X1)
% 0.49/0.67           | (r1_xboole_0 @ sk_B @ X0)
% 0.49/0.67           | ~ (r1_xboole_0 @ k1_xboole_0 @ X2)
% 0.49/0.67           | ~ (r2_hidden @ 
% 0.49/0.67                (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ X2)))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.67  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.49/0.67      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.67  thf('59', plain,
% 0.49/0.67      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67          ((r1_xboole_0 @ sk_A @ X1)
% 0.49/0.67           | (r1_xboole_0 @ sk_B @ X0)
% 0.49/0.67           | ~ (r2_hidden @ 
% 0.49/0.67                (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ X2)))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('demod', [status(thm)], ['57', '58'])).
% 0.49/0.67  thf('60', plain,
% 0.49/0.67      ((![X0 : $i, X1 : $i]:
% 0.49/0.67          ((r1_xboole_0 @ sk_A @ X1)
% 0.49/0.67           | (r1_xboole_0 @ sk_B @ X0)
% 0.49/0.67           | (r1_xboole_0 @ sk_B @ X0)
% 0.49/0.67           | (r1_xboole_0 @ sk_A @ X1)))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['54', '59'])).
% 0.49/0.67  thf('61', plain,
% 0.49/0.67      ((![X0 : $i, X1 : $i]:
% 0.49/0.67          ((r1_xboole_0 @ sk_B @ X0) | (r1_xboole_0 @ sk_A @ X1)))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['60'])).
% 0.49/0.67  thf(t66_xboole_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.49/0.67       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.49/0.67  thf('62', plain,
% 0.49/0.67      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X6))),
% 0.49/0.67      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.49/0.67  thf('63', plain,
% 0.49/0.67      ((![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ((sk_B) = (k1_xboole_0))))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['61', '62'])).
% 0.49/0.67  thf('64', plain,
% 0.49/0.67      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X6))),
% 0.49/0.67      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.49/0.67  thf('65', plain,
% 0.49/0.67      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.49/0.67         <= ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['63', '64'])).
% 0.49/0.67  thf('66', plain,
% 0.49/0.67      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['0'])).
% 0.49/0.67  thf('67', plain,
% 0.49/0.67      (((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.49/0.67         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['65', '66'])).
% 0.49/0.67  thf('68', plain,
% 0.49/0.67      ((((sk_A) = (k1_xboole_0)))
% 0.49/0.67         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['67'])).
% 0.49/0.67  thf('69', plain,
% 0.49/0.67      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['41'])).
% 0.49/0.67  thf('70', plain,
% 0.49/0.67      ((((sk_A) != (sk_A)))
% 0.49/0.67         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.49/0.67             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.49/0.67             (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['68', '69'])).
% 0.49/0.67  thf('71', plain,
% 0.49/0.67      ((((sk_A) = (k1_xboole_0))) | 
% 0.49/0.67       ~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.49/0.67       (((sk_B) = (k1_xboole_0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['70'])).
% 0.49/0.67  thf('72', plain,
% 0.49/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('73', plain,
% 0.49/0.67      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [t4_boole])).
% 0.49/0.67  thf('74', plain,
% 0.49/0.67      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 0.49/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['72', '73'])).
% 0.49/0.67  thf('75', plain,
% 0.49/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('76', plain,
% 0.49/0.67      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 0.49/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('demod', [status(thm)], ['74', '75'])).
% 0.49/0.67  thf('77', plain,
% 0.49/0.67      (![X7 : $i, X9 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X7 @ X9) | ((k4_xboole_0 @ X7 @ X9) != (X7)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.49/0.67  thf('78', plain,
% 0.49/0.67      ((![X0 : $i]: (((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ X0)))
% 0.49/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['76', '77'])).
% 0.49/0.67  thf('79', plain,
% 0.49/0.67      ((![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['78'])).
% 0.49/0.67  thf('80', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('simplify', [status(thm)], ['15'])).
% 0.49/0.67  thf('81', plain,
% 0.49/0.67      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['79', '80'])).
% 0.49/0.67  thf('82', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.49/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.67  thf('83', plain,
% 0.49/0.67      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.49/0.67         (((X23) = (k2_zfmisc_1 @ X20 @ X19))
% 0.49/0.67          | (zip_tseitin_0 @ (sk_F @ X23 @ X19 @ X20) @ 
% 0.49/0.67             (sk_E @ X23 @ X19 @ X20) @ (sk_D @ X23 @ X19 @ X20) @ X19 @ X20)
% 0.49/0.67          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.67  thf('84', plain,
% 0.49/0.67      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.49/0.67         ((r2_hidden @ X10 @ X14)
% 0.49/0.67          | ~ (zip_tseitin_0 @ X11 @ X10 @ X12 @ X13 @ X14))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.67  thf('85', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.67          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['83', '84'])).
% 0.49/0.67  thf('86', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.49/0.67          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.67          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['83', '84'])).
% 0.49/0.67  thf('87', plain,
% 0.49/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.49/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('88', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.49/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.49/0.67          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.49/0.67      inference('sup-', [status(thm)], ['86', '87'])).
% 0.49/0.67  thf('89', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.49/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.67          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1))),
% 0.49/0.67      inference('sup-', [status(thm)], ['85', '88'])).
% 0.49/0.67  thf('90', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         (~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.67          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.49/0.67          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1))),
% 0.49/0.67      inference('simplify', [status(thm)], ['89'])).
% 0.49/0.67  thf('91', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.49/0.67          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['82', '90'])).
% 0.49/0.67  thf('92', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.49/0.67          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['82', '90'])).
% 0.49/0.67  thf('93', plain,
% 0.49/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.49/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.67  thf('94', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.49/0.67          | ~ (r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 0.49/0.67      inference('sup-', [status(thm)], ['92', '93'])).
% 0.49/0.67  thf('95', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.67          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.49/0.67          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['91', '94'])).
% 0.49/0.67  thf('96', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['95'])).
% 0.49/0.67  thf('97', plain,
% 0.49/0.67      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.49/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['81', '96'])).
% 0.49/0.67  thf('98', plain,
% 0.49/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('99', plain,
% 0.49/0.67      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.49/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('demod', [status(thm)], ['97', '98'])).
% 0.49/0.67  thf('100', plain,
% 0.49/0.67      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.49/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['41'])).
% 0.49/0.67  thf('101', plain,
% 0.49/0.67      ((((sk_A) != (k1_xboole_0)))
% 0.49/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.67             (((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['99', '100'])).
% 0.49/0.67  thf('102', plain,
% 0.49/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('103', plain,
% 0.49/0.67      ((((sk_A) != (sk_A)))
% 0.49/0.67         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.49/0.67             (((sk_A) = (k1_xboole_0))))),
% 0.49/0.67      inference('demod', [status(thm)], ['101', '102'])).
% 0.49/0.67  thf('104', plain,
% 0.49/0.67      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.49/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['103'])).
% 0.49/0.67  thf('105', plain,
% 0.49/0.67      ((((sk_A) = (k1_xboole_0))) | 
% 0.49/0.67       (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.49/0.67       (((sk_B) = (k1_xboole_0)))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('106', plain, ($false),
% 0.49/0.67      inference('sat_resolution*', [status(thm)],
% 0.49/0.67                ['1', '46', '47', '71', '104', '105'])).
% 0.49/0.67  
% 0.49/0.67  % SZS output end Refutation
% 0.49/0.67  
% 0.49/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
