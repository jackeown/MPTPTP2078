%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ojSYbU2VNK

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 222 expanded)
%              Number of leaves         :   26 (  78 expanded)
%              Depth                    :   26
%              Number of atoms          :  913 (2478 expanded)
%              Number of equality atoms :   41 ( 100 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

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

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X29 ) )
      | ~ ( r2_hidden @ X27 @ X29 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_D_1 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ X0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X1 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ X1 ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_A @ X1 )
        | ~ ( r1_xboole_0 @ sk_A @ X0 )
        | ( r1_xboole_0 @ sk_A @ X1 ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ sk_A @ X0 )
        | ( r1_xboole_0 @ sk_A @ X1 ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_C_2 )
      | ( r1_tarski @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_C_2 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['17'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X1 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('42',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ sk_B @ X1 )
        | ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_B @ X1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ( r1_xboole_0 @ sk_B @ X1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ X0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
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

thf('53',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ( X22
        = ( k2_zfmisc_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X22 @ X18 @ X19 ) @ ( sk_E @ X22 @ X18 @ X19 ) @ ( sk_D @ X22 @ X18 @ X19 ) @ X18 @ X19 )
      | ( r2_hidden @ ( sk_D @ X22 @ X18 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X12 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('57',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('63',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['51','66'])).

thf('68',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['17'])).

thf('72',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference(simpl_trail,[status(thm)],['27','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['1','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('76',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('77',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X31 @ X30 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['79'])).

thf('81',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('82',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X32 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','80','82'])).

thf('84',plain,(
    $false ),
    inference(simplify,[status(thm)],['83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ojSYbU2VNK
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 143 iterations in 0.113s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.57  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.37/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.57  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.37/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(t138_zfmisc_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.37/0.57       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.37/0.57          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.37/0.57  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.57  thf('1', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.57  thf(t3_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf(d3_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf(l54_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.37/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 0.37/0.57         ((r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X29))
% 0.37/0.57          | ~ (r2_hidden @ X27 @ X29)
% 0.37/0.57          | ~ (r2_hidden @ X25 @ X26))),
% 0.37/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X0 @ X1)
% 0.37/0.57          | ~ (r2_hidden @ X3 @ X2)
% 0.37/0.57          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.37/0.57             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.37/0.57             (k2_zfmisc_1 @ X0 @ X2))
% 0.37/0.57          | (r1_tarski @ X2 @ X3))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '6'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.37/0.57        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X0 @ X2)
% 0.37/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ X0)
% 0.37/0.57          | (r1_tarski @ sk_A @ X1)
% 0.37/0.57          | (r2_hidden @ 
% 0.37/0.57             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.37/0.57             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.57         ((r2_hidden @ X27 @ X28)
% 0.37/0.57          | ~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X28)))),
% 0.37/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_A @ X1)
% 0.37/0.57          | (r1_tarski @ sk_B @ X0)
% 0.37/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_D_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ sk_D_1)
% 0.37/0.57          | (r1_tarski @ sk_A @ X0)
% 0.37/0.57          | (r1_tarski @ sk_B @ sk_D_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ sk_D_1))),
% 0.37/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.37/0.57      inference('split', [status(esa)], ['17'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      ((![X0 : $i]: (r1_tarski @ sk_A @ X0))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['16', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X0 @ X2)
% 0.37/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]:
% 0.37/0.57          ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]:
% 0.37/0.57          ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ X1)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['2', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.57          | ~ (r2_hidden @ X6 @ X7)
% 0.37/0.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.57          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]:
% 0.37/0.57          ((r1_xboole_0 @ sk_A @ X1)
% 0.37/0.57           | ~ (r1_xboole_0 @ sk_A @ X0)
% 0.37/0.57           | (r1_xboole_0 @ sk_A @ X1)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['22', '25'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]:
% 0.37/0.57          (~ (r1_xboole_0 @ sk_A @ X0) | (r1_xboole_0 @ sk_A @ X1)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.57  thf('28', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ X0)
% 0.37/0.57          | (r1_tarski @ sk_A @ X1)
% 0.37/0.57          | (r2_hidden @ 
% 0.37/0.57             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.37/0.57             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.57         ((r2_hidden @ X25 @ X26)
% 0.37/0.57          | ~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X28)))),
% 0.37/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_A @ X1)
% 0.37/0.57          | (r1_tarski @ sk_B @ X0)
% 0.37/0.57          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_C_2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ X0)
% 0.37/0.57          | (r1_tarski @ sk_A @ sk_C_2)
% 0.37/0.57          | (r1_tarski @ sk_A @ sk_C_2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X0 : $i]: ((r1_tarski @ sk_A @ sk_C_2) | (r1_tarski @ sk_B @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('split', [status(esa)], ['17'])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X0 @ X2)
% 0.37/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]:
% 0.37/0.57          ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_B)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]:
% 0.37/0.57          ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X1)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['29', '39'])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.57          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]:
% 0.37/0.57          ((r1_xboole_0 @ sk_B @ X1)
% 0.37/0.57           | ~ (r1_xboole_0 @ sk_B @ X0)
% 0.37/0.57           | (r1_xboole_0 @ sk_B @ X1)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      ((![X0 : $i, X1 : $i]:
% 0.37/0.57          (~ (r1_xboole_0 @ sk_B @ X0) | (r1_xboole_0 @ sk_B @ X1)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ X0))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['28', '43'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.57          | ~ (r2_hidden @ X6 @ X7)
% 0.37/0.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X1 @ X0)
% 0.37/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.57          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.57  thf('49', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.57          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.37/0.57          | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['45', '48'])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('simplify', [status(thm)], ['49'])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      ((![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['44', '50'])).
% 0.37/0.57  thf('52', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.57  thf(d2_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.37/0.57       ( ![D:$i]:
% 0.37/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.57           ( ?[E:$i,F:$i]:
% 0.37/0.57             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.37/0.57               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.37/0.57  thf(zf_stmt_2, axiom,
% 0.37/0.57    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.37/0.57     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.37/0.57       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.37/0.57         ( r2_hidden @ E @ A ) ) ))).
% 0.37/0.57  thf(zf_stmt_3, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.37/0.57       ( ![D:$i]:
% 0.37/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.57           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.37/0.57         (((X22) = (k2_zfmisc_1 @ X19 @ X18))
% 0.37/0.57          | (zip_tseitin_0 @ (sk_F @ X22 @ X18 @ X19) @ 
% 0.37/0.57             (sk_E @ X22 @ X18 @ X19) @ (sk_D @ X22 @ X18 @ X19) @ X18 @ X19)
% 0.37/0.57          | (r2_hidden @ (sk_D @ X22 @ X18 @ X19) @ X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.57  thf('54', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.57         ((r2_hidden @ X10 @ X12)
% 0.37/0.57          | ~ (zip_tseitin_0 @ X10 @ X9 @ X11 @ X12 @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.37/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.37/0.57          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.57  thf('56', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.37/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.37/0.57          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.57  thf('57', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.57          | ~ (r2_hidden @ X6 @ X7)
% 0.37/0.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.37/0.57          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.37/0.57          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.37/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.37/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.37/0.57          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.37/0.57          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.37/0.57          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.37/0.57          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['55', '58'])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r1_xboole_0 @ X0 @ X0)
% 0.37/0.57          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.37/0.57          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.37/0.57      inference('simplify', [status(thm)], ['59'])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.37/0.57          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['52', '60'])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.37/0.57          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['52', '60'])).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.57          | ~ (r2_hidden @ X6 @ X7)
% 0.37/0.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.37/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.57          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.37/0.57          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.37/0.57          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['61', '64'])).
% 0.37/0.57  thf('66', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['65'])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      ((![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.37/0.57         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['51', '66'])).
% 0.37/0.57  thf('68', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.57  thf('70', plain, (((r1_tarski @ sk_A @ sk_C_2))),
% 0.37/0.57      inference('simplify', [status(thm)], ['69'])).
% 0.37/0.57  thf('71', plain,
% 0.37/0.57      (~ ((r1_tarski @ sk_B @ sk_D_1)) | ~ ((r1_tarski @ sk_A @ sk_C_2))),
% 0.37/0.57      inference('split', [status(esa)], ['17'])).
% 0.37/0.57  thf('72', plain, (~ ((r1_tarski @ sk_B @ sk_D_1))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.37/0.57  thf('73', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r1_xboole_0 @ sk_A @ X0) | (r1_xboole_0 @ sk_A @ X1))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['27', '72'])).
% 0.37/0.57  thf('74', plain, (![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '73'])).
% 0.37/0.57  thf('75', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['65'])).
% 0.37/0.57  thf('76', plain, (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['74', '75'])).
% 0.37/0.57  thf(t113_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.57  thf('77', plain,
% 0.37/0.57      (![X30 : $i, X31 : $i]:
% 0.37/0.57         (((X30) = (k1_xboole_0))
% 0.37/0.58          | ((X31) = (k1_xboole_0))
% 0.37/0.58          | ((k2_zfmisc_1 @ X31 @ X30) != (k1_xboole_0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.58  thf('78', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.58          | ((X0) = (k1_xboole_0))
% 0.37/0.58          | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.58  thf('79', plain,
% 0.37/0.58      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['78'])).
% 0.37/0.58  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.58      inference('condensation', [status(thm)], ['79'])).
% 0.37/0.58  thf('81', plain,
% 0.37/0.58      (![X31 : $i, X32 : $i]:
% 0.37/0.58         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 0.37/0.58          | ((X31) != (k1_xboole_0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.58  thf('82', plain,
% 0.37/0.58      (![X32 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X32) = (k1_xboole_0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['81'])).
% 0.37/0.58  thf('83', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '80', '82'])).
% 0.37/0.58  thf('84', plain, ($false), inference('simplify', [status(thm)], ['83'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
