%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7THaZdK1sa

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:15 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 125 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  887 (1636 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :   28 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X20 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X16 @ X13 @ X14 ) @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ( X15
       != ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X16 @ X13 @ X14 ) @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) @ ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X4 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( X17
        = ( k2_zfmisc_1 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X17 @ X13 @ X14 ) @ ( sk_E @ X17 @ X13 @ X14 ) @ ( sk_D @ X17 @ X13 @ X14 ) @ X13 @ X14 )
      | ( r2_hidden @ ( sk_D @ X17 @ X13 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X3 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ sk_A @ sk_B )
          = ( k2_zfmisc_1 @ X1 @ X0 ) )
        | ( r2_hidden @ ( sk_F @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 @ X1 ) @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k3_xboole_0 @ sk_A @ sk_B )
          = ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        | ~ ( r1_xboole_0 @ X1 @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X20 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X20 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X20 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X20 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X20 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X5 @ X4 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ X5 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ X4 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X7 @ X6 ) ) @ ( k3_xboole_0 @ X5 @ X4 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ X7 ) @ X5 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ X6 ) @ X4 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X9 @ X8 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ X7 @ X6 ) ) @ ( k3_xboole_0 @ X5 @ X4 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ X7 ) @ X5 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) @ X6 ) @ X4 ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X11 @ X10 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X9 @ X8 ) ) ) @ ( k3_xboole_0 @ X7 @ X6 ) ) @ ( k3_xboole_0 @ X5 @ X4 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ X9 ) ) @ X7 ) @ X5 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ X8 ) ) @ X6 ) @ X4 ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
        ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
        | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) @ X3 ) ) @ X1 ) @ sk_A ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) @ X2 ) ) @ X0 ) @ sk_B ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) @ ( sk_E_1 @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_A ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ! [X10: $i] :
        ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D_1 )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('47',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i] :
      ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7THaZdK1sa
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.93  % Solved by: fo/fo7.sh
% 0.74/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.93  % done 216 iterations in 0.473s
% 0.74/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.93  % SZS output start Refutation
% 0.74/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.74/0.93  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.74/0.93  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.74/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.93  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.74/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.74/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.74/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.74/0.93  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.74/0.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.74/0.93  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.74/0.93  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.74/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.93  thf(t127_zfmisc_1, conjecture,
% 0.74/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.93     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.74/0.93       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.74/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.93    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.93        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.74/0.93          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.74/0.93    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 0.74/0.93  thf('0', plain,
% 0.74/0.93      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.74/0.93          (k2_zfmisc_1 @ sk_B @ sk_D_1))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t123_zfmisc_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.93     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.74/0.93       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.74/0.93  thf('1', plain,
% 0.74/0.93      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.74/0.93         ((k2_zfmisc_1 @ (k3_xboole_0 @ X20 @ X22) @ (k3_xboole_0 @ X21 @ X23))
% 0.74/0.93           = (k3_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 0.74/0.93              (k2_zfmisc_1 @ X22 @ X23)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.74/0.93  thf(t4_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.74/0.93            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.74/0.93  thf('2', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X0 @ X1)
% 0.74/0.93          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.74/0.93  thf('3', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((r2_hidden @ 
% 0.74/0.93           (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.74/0.93           (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.74/0.93          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['1', '2'])).
% 0.74/0.93  thf(d2_zfmisc_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.74/0.93       ( ![D:$i]:
% 0.74/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.74/0.93           ( ?[E:$i,F:$i]:
% 0.74/0.93             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.74/0.93               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.74/0.93  thf(zf_stmt_2, axiom,
% 0.74/0.93    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.74/0.93     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.74/0.93       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.74/0.93         ( r2_hidden @ E @ A ) ) ))).
% 0.74/0.93  thf(zf_stmt_3, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.74/0.93       ( ![D:$i]:
% 0.74/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.74/0.93           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.74/0.93  thf('4', plain,
% 0.74/0.93      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X16 @ X15)
% 0.74/0.93          | (zip_tseitin_0 @ (sk_F_1 @ X16 @ X13 @ X14) @ 
% 0.74/0.93             (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.74/0.93          | ((X15) != (k2_zfmisc_1 @ X14 @ X13)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.74/0.93  thf('5', plain,
% 0.74/0.93      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.74/0.93         ((zip_tseitin_0 @ (sk_F_1 @ X16 @ X13 @ X14) @ 
% 0.74/0.93           (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.74/0.93          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X14 @ X13)))),
% 0.74/0.93      inference('simplify', [status(thm)], ['4'])).
% 0.74/0.93  thf('6', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0))
% 0.74/0.93          | (zip_tseitin_0 @ 
% 0.74/0.93             (sk_F_1 @ 
% 0.74/0.93              (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.74/0.93              (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2)) @ 
% 0.74/0.93             (sk_E_1 @ 
% 0.74/0.93              (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.74/0.93              (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2)) @ 
% 0.74/0.93             (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.74/0.93             (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['3', '5'])).
% 0.74/0.93  thf('7', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.74/0.93         ((r2_hidden @ X4 @ X8) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.93  thf('8', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X3) @ (k2_zfmisc_1 @ X0 @ X2))
% 0.74/0.93          | (r2_hidden @ 
% 0.74/0.93             (sk_E_1 @ 
% 0.74/0.93              (sk_C @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)) @ 
% 0.74/0.93              (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.74/0.93             (k3_xboole_0 @ X1 @ X0)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['6', '7'])).
% 0.74/0.93  thf('9', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('10', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('split', [status(esa)], ['9'])).
% 0.74/0.93  thf('11', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('split', [status(esa)], ['9'])).
% 0.74/0.93  thf('12', plain,
% 0.74/0.93      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.74/0.93         (((X17) = (k2_zfmisc_1 @ X14 @ X13))
% 0.74/0.93          | (zip_tseitin_0 @ (sk_F @ X17 @ X13 @ X14) @ 
% 0.74/0.93             (sk_E @ X17 @ X13 @ X14) @ (sk_D @ X17 @ X13 @ X14) @ X13 @ X14)
% 0.74/0.93          | (r2_hidden @ (sk_D @ X17 @ X13 @ X14) @ X17))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.74/0.93  thf('13', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.74/0.93         ((r2_hidden @ X5 @ X7) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.93  thf('14', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.74/0.93          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.74/0.93          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.74/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.74/0.93  thf('15', plain,
% 0.74/0.93      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.74/0.93          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.74/0.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.74/0.93  thf('16', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((r2_hidden @ (sk_F @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X3)
% 0.74/0.93          | ((k3_xboole_0 @ X1 @ X0) = (k2_zfmisc_1 @ X2 @ X3))
% 0.74/0.93          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.93  thf('17', plain,
% 0.74/0.93      ((![X0 : $i, X1 : $i]:
% 0.74/0.93          (((k3_xboole_0 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X1 @ X0))
% 0.74/0.93           | (r2_hidden @ (sk_F @ (k3_xboole_0 @ sk_A @ sk_B) @ X0 @ X1) @ X0)))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['11', '16'])).
% 0.74/0.93  thf('18', plain,
% 0.74/0.93      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.74/0.93          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.74/0.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.74/0.93  thf('19', plain,
% 0.74/0.93      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93          (((k3_xboole_0 @ sk_A @ sk_B)
% 0.74/0.93             = (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.74/0.93           | ~ (r1_xboole_0 @ X1 @ X0)))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['17', '18'])).
% 0.74/0.93  thf('20', plain,
% 0.74/0.93      ((![X0 : $i]:
% 0.74/0.93          ((k3_xboole_0 @ sk_A @ sk_B)
% 0.74/0.93            = (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B))))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['10', '19'])).
% 0.74/0.93  thf('21', plain,
% 0.74/0.93      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.74/0.93         ((k2_zfmisc_1 @ (k3_xboole_0 @ X20 @ X22) @ (k3_xboole_0 @ X21 @ X23))
% 0.74/0.93           = (k3_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 0.74/0.93              (k2_zfmisc_1 @ X22 @ X23)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.74/0.93  thf('22', plain,
% 0.74/0.93      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.74/0.93         ((k2_zfmisc_1 @ (k3_xboole_0 @ X20 @ X22) @ (k3_xboole_0 @ X21 @ X23))
% 0.74/0.93           = (k3_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 0.74/0.93              (k2_zfmisc_1 @ X22 @ X23)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.74/0.93  thf('23', plain,
% 0.74/0.93      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.74/0.93         ((k2_zfmisc_1 @ (k3_xboole_0 @ X20 @ X22) @ (k3_xboole_0 @ X21 @ X23))
% 0.74/0.93           = (k3_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 0.74/0.93              (k2_zfmisc_1 @ X22 @ X23)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.74/0.93  thf('24', plain,
% 0.74/0.93      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.74/0.93         ((k2_zfmisc_1 @ (k3_xboole_0 @ X20 @ X22) @ (k3_xboole_0 @ X21 @ X23))
% 0.74/0.93           = (k3_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 0.74/0.93              (k2_zfmisc_1 @ X22 @ X23)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.74/0.93  thf('25', plain,
% 0.74/0.93      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.74/0.93         ((k2_zfmisc_1 @ (k3_xboole_0 @ X20 @ X22) @ (k3_xboole_0 @ X21 @ X23))
% 0.74/0.93           = (k3_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 0.74/0.93              (k2_zfmisc_1 @ X22 @ X23)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.74/0.93  thf('26', plain,
% 0.74/0.93      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.74/0.93          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.74/0.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.74/0.93  thf('27', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X4 @ 
% 0.74/0.93             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.74/0.93          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['25', '26'])).
% 0.74/0.93  thf('28', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X6 @ 
% 0.74/0.93             (k2_zfmisc_1 @ 
% 0.74/0.93              (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.74/0.93              (k3_xboole_0 @ X5 @ X4)))
% 0.74/0.93          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1) @ X5) @ 
% 0.74/0.93               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0) @ X4)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['24', '27'])).
% 0.74/0.93  thf('29', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.74/0.93         X7 : $i, X8 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X8 @ 
% 0.74/0.93             (k2_zfmisc_1 @ 
% 0.74/0.93              (k2_zfmisc_1 @ 
% 0.74/0.93               (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.74/0.93               (k3_xboole_0 @ X7 @ X6)) @ 
% 0.74/0.93              (k3_xboole_0 @ X5 @ X4)))
% 0.74/0.93          | ~ (r1_xboole_0 @ 
% 0.74/0.93               (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1) @ X7) @ X5) @ 
% 0.74/0.93               (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0) @ X6) @ X4)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['23', '28'])).
% 0.74/0.93  thf('30', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.74/0.93         X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X10 @ 
% 0.74/0.93             (k2_zfmisc_1 @ 
% 0.74/0.93              (k2_zfmisc_1 @ 
% 0.74/0.93               (k2_zfmisc_1 @ (k3_xboole_0 @ X9 @ X8) @ 
% 0.74/0.93                (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ 
% 0.74/0.93                 (k3_xboole_0 @ X1 @ X0))) @ 
% 0.74/0.93               (k3_xboole_0 @ X7 @ X6)) @ 
% 0.74/0.93              (k3_xboole_0 @ X5 @ X4)))
% 0.74/0.93          | ~ (r1_xboole_0 @ 
% 0.74/0.93               (k2_zfmisc_1 @ 
% 0.74/0.93                (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.74/0.93                 X7) @ 
% 0.74/0.93                X5) @ 
% 0.74/0.93               (k2_zfmisc_1 @ 
% 0.74/0.93                (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ (k2_zfmisc_1 @ X2 @ X0)) @ 
% 0.74/0.93                 X6) @ 
% 0.74/0.93                X4)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['22', '29'])).
% 0.74/0.93  thf('31', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.74/0.93         X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X12 @ 
% 0.74/0.93             (k2_zfmisc_1 @ 
% 0.74/0.93              (k2_zfmisc_1 @ 
% 0.74/0.93               (k2_zfmisc_1 @ (k3_xboole_0 @ X11 @ X10) @ 
% 0.74/0.93                (k2_zfmisc_1 @ 
% 0.74/0.93                 (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ 
% 0.74/0.93                  (k3_xboole_0 @ X1 @ X0)) @ 
% 0.74/0.93                 (k3_xboole_0 @ X9 @ X8))) @ 
% 0.74/0.93               (k3_xboole_0 @ X7 @ X6)) @ 
% 0.74/0.93              (k3_xboole_0 @ X5 @ X4)))
% 0.74/0.93          | ~ (r1_xboole_0 @ 
% 0.74/0.93               (k2_zfmisc_1 @ 
% 0.74/0.93                (k2_zfmisc_1 @ 
% 0.74/0.93                 (k2_zfmisc_1 @ X11 @ 
% 0.74/0.93                  (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1) @ X9)) @ 
% 0.74/0.93                 X7) @ 
% 0.74/0.93                X5) @ 
% 0.74/0.93               (k2_zfmisc_1 @ 
% 0.74/0.93                (k2_zfmisc_1 @ 
% 0.74/0.93                 (k2_zfmisc_1 @ X10 @ 
% 0.74/0.93                  (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0) @ X8)) @ 
% 0.74/0.93                 X6) @ 
% 0.74/0.93                X4)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['21', '30'])).
% 0.74/0.93  thf('32', plain,
% 0.74/0.93      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.74/0.93          X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.74/0.93          (~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.74/0.93           | ~ (r1_xboole_0 @ 
% 0.74/0.93                (k2_zfmisc_1 @ 
% 0.74/0.93                 (k2_zfmisc_1 @ 
% 0.74/0.93                  (k2_zfmisc_1 @ X9 @ 
% 0.74/0.93                   (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5) @ X3)) @ 
% 0.74/0.93                  X1) @ 
% 0.74/0.93                 sk_A) @ 
% 0.74/0.93                (k2_zfmisc_1 @ 
% 0.74/0.93                 (k2_zfmisc_1 @ 
% 0.74/0.93                  (k2_zfmisc_1 @ X8 @ 
% 0.74/0.93                   (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4) @ X2)) @ 
% 0.74/0.93                  X0) @ 
% 0.74/0.93                 sk_B))))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['20', '31'])).
% 0.74/0.93  thf('33', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('split', [status(esa)], ['9'])).
% 0.74/0.93  thf('34', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0))
% 0.74/0.93          | (zip_tseitin_0 @ 
% 0.74/0.93             (sk_F_1 @ 
% 0.74/0.93              (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.74/0.93              (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2)) @ 
% 0.74/0.93             (sk_E_1 @ 
% 0.74/0.93              (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.74/0.93              (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2)) @ 
% 0.74/0.93             (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.74/0.93             (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['3', '5'])).
% 0.74/0.93  thf('35', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.74/0.93         ((r2_hidden @ X5 @ X7) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.93  thf('36', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X3) @ (k2_zfmisc_1 @ X0 @ X2))
% 0.74/0.93          | (r2_hidden @ 
% 0.74/0.93             (sk_F_1 @ 
% 0.74/0.93              (sk_C @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)) @ 
% 0.74/0.93              (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.74/0.93             (k3_xboole_0 @ X3 @ X2)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.74/0.93  thf('37', plain,
% 0.74/0.93      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.74/0.93          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.74/0.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.74/0.93  thf('38', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0))
% 0.74/0.93          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['36', '37'])).
% 0.74/0.93  thf('39', plain,
% 0.74/0.93      ((![X0 : $i, X1 : $i]:
% 0.74/0.93          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_A) @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['33', '38'])).
% 0.74/0.93  thf('40', plain,
% 0.74/0.93      ((![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('demod', [status(thm)], ['32', '39'])).
% 0.74/0.93  thf('41', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_C_1 @ sk_D_1)) <= (((r1_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 0.74/0.93      inference('split', [status(esa)], ['9'])).
% 0.74/0.93  thf('42', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0))
% 0.74/0.93          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['36', '37'])).
% 0.74/0.93  thf('43', plain,
% 0.74/0.93      ((![X0 : $i, X1 : $i]:
% 0.74/0.93          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 0.74/0.93           (k2_zfmisc_1 @ X0 @ sk_D_1)))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['41', '42'])).
% 0.74/0.93  thf('44', plain,
% 0.74/0.93      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.74/0.93          (k2_zfmisc_1 @ sk_B @ sk_D_1))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('45', plain, (~ ((r1_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.74/0.93      inference('sup-', [status(thm)], ['43', '44'])).
% 0.74/0.93  thf('46', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B)) | ((r1_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.74/0.93      inference('split', [status(esa)], ['9'])).
% 0.74/0.93  thf('47', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.93      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.74/0.93  thf('48', plain,
% 0.74/0.93      (![X10 : $i]: ~ (r2_hidden @ X10 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.93      inference('simpl_trail', [status(thm)], ['40', '47'])).
% 0.74/0.93  thf('49', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['8', '48'])).
% 0.74/0.93  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.74/0.93  
% 0.74/0.93  % SZS output end Refutation
% 0.74/0.93  
% 0.74/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
