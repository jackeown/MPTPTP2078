%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lLvvCljIis

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:02 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 362 expanded)
%              Number of leaves         :   24 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          : 1241 (3900 expanded)
%              Number of equality atoms :  161 ( 339 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('3',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ X1 @ X0 )
         != sk_B_1 )
        | ( r1_xboole_0 @ X1 @ X0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( r1_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

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

thf('31',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ( X22
        = ( k2_zfmisc_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X22 @ X18 @ X19 ) @ ( sk_E @ X22 @ X18 @ X19 ) @ ( sk_D @ X22 @ X18 @ X19 ) @ X18 @ X19 )
      | ( r2_hidden @ ( sk_D @ X22 @ X18 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X12 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('41',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','44'])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('56',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('57',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X29 ) )
      | ~ ( r2_hidden @ X27 @ X29 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('63',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('68',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('74',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('78',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('79',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ X1 @ X0 )
         != sk_A )
        | ( r1_xboole_0 @ X1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_A )
        | ( r1_xboole_0 @ X0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_A @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('87',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ( X22
        = ( k2_zfmisc_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X22 @ X18 @ X19 ) @ ( sk_E @ X22 @ X18 @ X19 ) @ ( sk_D @ X22 @ X18 @ X19 ) @ X18 @ X19 )
      | ( r2_hidden @ ( sk_D @ X22 @ X18 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('88',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X9 @ X13 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('91',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','94'])).

thf('97',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','100'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('105',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('107',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('110',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','53','54','75','108','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lLvvCljIis
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.80  % Solved by: fo/fo7.sh
% 0.57/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.80  % done 558 iterations in 0.344s
% 0.57/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.80  % SZS output start Refutation
% 0.57/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.57/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.57/0.80  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.57/0.80  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.57/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.80  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.57/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.57/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.57/0.80  thf(t113_zfmisc_1, conjecture,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.57/0.80       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.57/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.80    (~( ![A:$i,B:$i]:
% 0.57/0.80        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.57/0.80          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.57/0.80    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.57/0.80  thf('0', plain,
% 0.57/0.80      ((((sk_B_1) != (k1_xboole_0))
% 0.57/0.80        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('1', plain,
% 0.57/0.80      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.57/0.80       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.57/0.80      inference('split', [status(esa)], ['0'])).
% 0.57/0.80  thf(idempotence_k3_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.57/0.80  thf('2', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.57/0.80  thf('3', plain,
% 0.57/0.80      ((((sk_B_1) = (k1_xboole_0))
% 0.57/0.80        | ((sk_A) = (k1_xboole_0))
% 0.57/0.80        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('4', plain,
% 0.57/0.80      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.80      inference('split', [status(esa)], ['3'])).
% 0.57/0.80  thf(d7_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.57/0.80       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.57/0.80  thf('5', plain,
% 0.57/0.80      (![X0 : $i, X2 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.57/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.80  thf('6', plain,
% 0.57/0.80      ((![X0 : $i, X1 : $i]:
% 0.57/0.80          (((k3_xboole_0 @ X1 @ X0) != (sk_B_1)) | (r1_xboole_0 @ X1 @ X0)))
% 0.57/0.80         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.57/0.80  thf('7', plain,
% 0.57/0.80      ((![X0 : $i]: (((X0) != (sk_B_1)) | (r1_xboole_0 @ X0 @ X0)))
% 0.57/0.80         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.80      inference('sup-', [status(thm)], ['2', '6'])).
% 0.57/0.80  thf('8', plain,
% 0.57/0.80      (((r1_xboole_0 @ sk_B_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.80      inference('simplify', [status(thm)], ['7'])).
% 0.57/0.80  thf(t3_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.57/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.57/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.57/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.57/0.80  thf('9', plain,
% 0.57/0.80      (![X4 : $i, X5 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.80  thf('10', plain,
% 0.57/0.80      (![X4 : $i, X5 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.80  thf('11', plain,
% 0.57/0.80      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.80         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.80          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.80          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.80  thf('12', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.57/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.57/0.80          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.57/0.80      inference('sup-', [status(thm)], ['10', '11'])).
% 0.57/0.80  thf('13', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.57/0.80          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.80          | (r1_xboole_0 @ X0 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['9', '12'])).
% 0.57/0.80  thf('14', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.57/0.80      inference('simplify', [status(thm)], ['13'])).
% 0.57/0.80  thf('15', plain,
% 0.57/0.80      ((![X0 : $i]: (r1_xboole_0 @ sk_B_1 @ X0))
% 0.57/0.80         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.80      inference('sup-', [status(thm)], ['8', '14'])).
% 0.57/0.80  thf('16', plain,
% 0.57/0.80      (![X4 : $i, X5 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.80  thf('17', plain,
% 0.57/0.80      (![X4 : $i, X5 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.80  thf('18', plain,
% 0.57/0.80      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.80         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.80          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.80          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.80  thf('19', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X1 @ X0)
% 0.57/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.57/0.80          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.57/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.57/0.80  thf('20', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.57/0.80          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.57/0.80          | (r1_xboole_0 @ X0 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['16', '19'])).
% 0.57/0.80  thf('21', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.57/0.80      inference('simplify', [status(thm)], ['20'])).
% 0.57/0.80  thf('22', plain,
% 0.57/0.80      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B_1))
% 0.57/0.80         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.80      inference('sup-', [status(thm)], ['15', '21'])).
% 0.57/0.80  thf('23', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.57/0.80  thf('24', plain,
% 0.57/0.80      (![X0 : $i, X2 : $i]:
% 0.57/0.81         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.57/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.81  thf('25', plain,
% 0.57/0.81      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.57/0.81  thf('26', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.57/0.81      inference('simplify', [status(thm)], ['25'])).
% 0.57/0.81  thf('27', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.57/0.81      inference('simplify', [status(thm)], ['13'])).
% 0.57/0.81  thf('28', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.57/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.57/0.81  thf('29', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.57/0.81      inference('simplify', [status(thm)], ['20'])).
% 0.57/0.81  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.81      inference('sup-', [status(thm)], ['28', '29'])).
% 0.57/0.81  thf(d2_zfmisc_1, axiom,
% 0.57/0.81    (![A:$i,B:$i,C:$i]:
% 0.57/0.81     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.57/0.81       ( ![D:$i]:
% 0.57/0.81         ( ( r2_hidden @ D @ C ) <=>
% 0.57/0.81           ( ?[E:$i,F:$i]:
% 0.57/0.81             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.57/0.81               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.57/0.81  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.57/0.81  thf(zf_stmt_2, axiom,
% 0.57/0.81    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.57/0.81     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.57/0.81       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.57/0.81         ( r2_hidden @ E @ A ) ) ))).
% 0.57/0.81  thf(zf_stmt_3, axiom,
% 0.57/0.81    (![A:$i,B:$i,C:$i]:
% 0.57/0.81     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.57/0.81       ( ![D:$i]:
% 0.57/0.81         ( ( r2_hidden @ D @ C ) <=>
% 0.57/0.81           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.57/0.81  thf('31', plain,
% 0.57/0.81      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.57/0.81         (((X22) = (k2_zfmisc_1 @ X19 @ X18))
% 0.57/0.81          | (zip_tseitin_0 @ (sk_F @ X22 @ X18 @ X19) @ 
% 0.57/0.81             (sk_E @ X22 @ X18 @ X19) @ (sk_D @ X22 @ X18 @ X19) @ X18 @ X19)
% 0.57/0.81          | (r2_hidden @ (sk_D @ X22 @ X18 @ X19) @ X22))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.81  thf('32', plain,
% 0.57/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.57/0.81         ((r2_hidden @ X10 @ X12)
% 0.57/0.81          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.81  thf('33', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.57/0.81          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.57/0.81  thf('34', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.57/0.81          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.57/0.81  thf('35', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('36', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.57/0.81          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.57/0.81      inference('sup-', [status(thm)], ['34', '35'])).
% 0.57/0.81  thf('37', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['33', '36'])).
% 0.57/0.81  thf('38', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.57/0.81      inference('simplify', [status(thm)], ['37'])).
% 0.57/0.81  thf('39', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['30', '38'])).
% 0.57/0.81  thf('40', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['30', '38'])).
% 0.57/0.81  thf('41', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('42', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.57/0.81          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['40', '41'])).
% 0.57/0.81  thf('43', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['39', '42'])).
% 0.57/0.81  thf('44', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['43'])).
% 0.57/0.81  thf('45', plain,
% 0.57/0.81      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.57/0.81         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['22', '44'])).
% 0.57/0.81  thf('46', plain,
% 0.57/0.81      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['3'])).
% 0.57/0.81  thf('47', plain,
% 0.57/0.81      ((![X0 : $i]: ((sk_B_1) = (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.57/0.81         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('demod', [status(thm)], ['45', '46'])).
% 0.57/0.81  thf('48', plain,
% 0.57/0.81      ((((sk_A) != (k1_xboole_0))
% 0.57/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.81  thf('49', plain,
% 0.57/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.57/0.81         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['48'])).
% 0.57/0.81  thf('50', plain,
% 0.57/0.81      ((((sk_B_1) != (k1_xboole_0)))
% 0.57/0.81         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.57/0.81             (((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['47', '49'])).
% 0.57/0.81  thf('51', plain,
% 0.57/0.81      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['3'])).
% 0.57/0.81  thf('52', plain,
% 0.57/0.81      ((((sk_B_1) != (sk_B_1)))
% 0.57/0.81         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.57/0.81             (((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('demod', [status(thm)], ['50', '51'])).
% 0.57/0.81  thf('53', plain,
% 0.57/0.81      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.57/0.81       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['52'])).
% 0.57/0.81  thf('54', plain,
% 0.57/0.81      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.57/0.81       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.57/0.81      inference('split', [status(esa)], ['48'])).
% 0.57/0.81  thf('55', plain,
% 0.57/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.57/0.81         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['3'])).
% 0.57/0.81  thf(t7_xboole_0, axiom,
% 0.57/0.81    (![A:$i]:
% 0.57/0.81     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.57/0.81          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.57/0.81  thf('56', plain,
% 0.57/0.81      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.57/0.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.81  thf('57', plain,
% 0.57/0.81      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.57/0.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.81  thf(l54_zfmisc_1, axiom,
% 0.57/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.81     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.57/0.81       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.57/0.81  thf('58', plain,
% 0.57/0.81      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 0.57/0.81         ((r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X29))
% 0.57/0.81          | ~ (r2_hidden @ X27 @ X29)
% 0.57/0.81          | ~ (r2_hidden @ X25 @ X26))),
% 0.57/0.81      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.57/0.81  thf('59', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (((X0) = (k1_xboole_0))
% 0.57/0.81          | ~ (r2_hidden @ X2 @ X1)
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['57', '58'])).
% 0.57/0.81  thf('60', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (((X0) = (k1_xboole_0))
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | ((X1) = (k1_xboole_0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['56', '59'])).
% 0.57/0.81  thf('61', plain,
% 0.57/0.81      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.57/0.81          k1_xboole_0)
% 0.57/0.81         | ((sk_B_1) = (k1_xboole_0))
% 0.57/0.81         | ((sk_A) = (k1_xboole_0))))
% 0.57/0.81         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup+', [status(thm)], ['55', '60'])).
% 0.57/0.81  thf('62', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (((X0) = (k1_xboole_0))
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | ((X1) = (k1_xboole_0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['56', '59'])).
% 0.57/0.81  thf('63', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('64', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (((X0) = (k1_xboole_0))
% 0.57/0.81          | ((X1) = (k1_xboole_0))
% 0.57/0.81          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.57/0.81          | ~ (r2_hidden @ (k4_tarski @ (sk_B @ X1) @ (sk_B @ X0)) @ X2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['62', '63'])).
% 0.57/0.81  thf('65', plain,
% 0.57/0.81      (((((sk_A) = (k1_xboole_0))
% 0.57/0.81         | ((sk_B_1) = (k1_xboole_0))
% 0.57/0.81         | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.57/0.81         | ((sk_A) = (k1_xboole_0))
% 0.57/0.81         | ((sk_B_1) = (k1_xboole_0))))
% 0.57/0.81         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['61', '64'])).
% 0.57/0.81  thf('66', plain,
% 0.57/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.57/0.81         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['3'])).
% 0.57/0.81  thf('67', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.57/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.57/0.81  thf('68', plain,
% 0.57/0.81      (((((sk_A) = (k1_xboole_0))
% 0.57/0.81         | ((sk_B_1) = (k1_xboole_0))
% 0.57/0.81         | ((sk_A) = (k1_xboole_0))
% 0.57/0.81         | ((sk_B_1) = (k1_xboole_0))))
% 0.57/0.81         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.57/0.81  thf('69', plain,
% 0.57/0.81      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.57/0.81         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('simplify', [status(thm)], ['68'])).
% 0.57/0.81  thf('70', plain,
% 0.57/0.81      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['0'])).
% 0.57/0.81  thf('71', plain,
% 0.57/0.81      (((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0))))
% 0.57/0.81         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.57/0.81             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['69', '70'])).
% 0.57/0.81  thf('72', plain,
% 0.57/0.81      ((((sk_A) = (k1_xboole_0)))
% 0.57/0.81         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.57/0.81             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('simplify', [status(thm)], ['71'])).
% 0.57/0.81  thf('73', plain,
% 0.57/0.81      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['48'])).
% 0.57/0.81  thf('74', plain,
% 0.57/0.81      ((((sk_A) != (sk_A)))
% 0.57/0.81         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.57/0.81             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.57/0.81             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['72', '73'])).
% 0.57/0.81  thf('75', plain,
% 0.57/0.81      ((((sk_A) = (k1_xboole_0))) | 
% 0.57/0.81       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.57/0.81       (((sk_B_1) = (k1_xboole_0)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['74'])).
% 0.57/0.81  thf('76', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.57/0.81      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.57/0.81  thf('77', plain,
% 0.57/0.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['3'])).
% 0.57/0.81  thf('78', plain,
% 0.57/0.81      (![X0 : $i, X2 : $i]:
% 0.57/0.81         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.57/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.81  thf('79', plain,
% 0.57/0.81      ((![X0 : $i, X1 : $i]:
% 0.57/0.81          (((k3_xboole_0 @ X1 @ X0) != (sk_A)) | (r1_xboole_0 @ X1 @ X0)))
% 0.57/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['77', '78'])).
% 0.57/0.81  thf('80', plain,
% 0.57/0.81      ((![X0 : $i]: (((X0) != (sk_A)) | (r1_xboole_0 @ X0 @ X0)))
% 0.57/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['76', '79'])).
% 0.57/0.81  thf('81', plain,
% 0.57/0.81      (((r1_xboole_0 @ sk_A @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('simplify', [status(thm)], ['80'])).
% 0.57/0.81  thf('82', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.57/0.81      inference('simplify', [status(thm)], ['13'])).
% 0.57/0.81  thf('83', plain,
% 0.57/0.81      ((![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['81', '82'])).
% 0.57/0.81  thf('84', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.57/0.81      inference('simplify', [status(thm)], ['20'])).
% 0.57/0.81  thf('85', plain,
% 0.57/0.81      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['83', '84'])).
% 0.57/0.81  thf('86', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.81      inference('sup-', [status(thm)], ['28', '29'])).
% 0.57/0.81  thf('87', plain,
% 0.57/0.81      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.57/0.81         (((X22) = (k2_zfmisc_1 @ X19 @ X18))
% 0.57/0.81          | (zip_tseitin_0 @ (sk_F @ X22 @ X18 @ X19) @ 
% 0.57/0.81             (sk_E @ X22 @ X18 @ X19) @ (sk_D @ X22 @ X18 @ X19) @ X18 @ X19)
% 0.57/0.81          | (r2_hidden @ (sk_D @ X22 @ X18 @ X19) @ X22))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.81  thf('88', plain,
% 0.57/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.57/0.81         ((r2_hidden @ X9 @ X13)
% 0.57/0.81          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.81  thf('89', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.57/0.81          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['87', '88'])).
% 0.57/0.81  thf('90', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.57/0.81          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['87', '88'])).
% 0.57/0.81  thf('91', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('92', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.57/0.81          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.57/0.81      inference('sup-', [status(thm)], ['90', '91'])).
% 0.57/0.81  thf('93', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['89', '92'])).
% 0.57/0.81  thf('94', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | (r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1))),
% 0.57/0.81      inference('simplify', [status(thm)], ['93'])).
% 0.57/0.81  thf('95', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['86', '94'])).
% 0.57/0.81  thf('96', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['86', '94'])).
% 0.57/0.81  thf('97', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('98', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.57/0.81          | ~ (r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['96', '97'])).
% 0.57/0.81  thf('99', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['95', '98'])).
% 0.57/0.81  thf('100', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['99'])).
% 0.57/0.81  thf('101', plain,
% 0.57/0.81      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.57/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['85', '100'])).
% 0.57/0.81  thf('102', plain,
% 0.57/0.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['3'])).
% 0.57/0.81  thf('103', plain,
% 0.57/0.81      ((![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0)))
% 0.57/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('demod', [status(thm)], ['101', '102'])).
% 0.57/0.81  thf('104', plain,
% 0.57/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.57/0.81         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['48'])).
% 0.57/0.81  thf('105', plain,
% 0.57/0.81      ((((sk_A) != (k1_xboole_0)))
% 0.57/0.81         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.57/0.81             (((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('sup-', [status(thm)], ['103', '104'])).
% 0.57/0.81  thf('106', plain,
% 0.57/0.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('split', [status(esa)], ['3'])).
% 0.57/0.81  thf('107', plain,
% 0.57/0.81      ((((sk_A) != (sk_A)))
% 0.57/0.81         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.57/0.81             (((sk_A) = (k1_xboole_0))))),
% 0.57/0.81      inference('demod', [status(thm)], ['105', '106'])).
% 0.57/0.81  thf('108', plain,
% 0.57/0.81      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.57/0.81       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['107'])).
% 0.57/0.81  thf('109', plain,
% 0.57/0.81      ((((sk_A) = (k1_xboole_0))) | 
% 0.57/0.81       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.57/0.81       (((sk_B_1) = (k1_xboole_0)))),
% 0.57/0.81      inference('split', [status(esa)], ['3'])).
% 0.57/0.81  thf('110', plain, ($false),
% 0.57/0.81      inference('sat_resolution*', [status(thm)],
% 0.57/0.81                ['1', '53', '54', '75', '108', '109'])).
% 0.57/0.81  
% 0.57/0.81  % SZS output end Refutation
% 0.57/0.81  
% 0.63/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
