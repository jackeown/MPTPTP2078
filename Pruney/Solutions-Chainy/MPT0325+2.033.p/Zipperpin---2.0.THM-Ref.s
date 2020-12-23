%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N2apLBvORg

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:44 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 182 expanded)
%              Number of leaves         :   29 (  68 expanded)
%              Depth                    :   24
%              Number of atoms          :  700 (1508 expanded)
%              Number of equality atoms :   43 (  88 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_zfmisc_1 @ X34 @ X35 )
        = k1_xboole_0 )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ X34 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X32 ) )
      | ~ ( r2_hidden @ X30 @ X32 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X32 ) )
      | ~ ( r2_hidden @ X30 @ X32 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('48',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_2 )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_A @ sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ X34 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('60',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['39','60'])).

thf('62',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['37','61'])).

thf('63',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_zfmisc_1 @ X34 @ X35 )
        = k1_xboole_0 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X35: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X35 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','62','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N2apLBvORg
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.82/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.05  % Solved by: fo/fo7.sh
% 0.82/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.05  % done 506 iterations in 0.584s
% 0.82/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.05  % SZS output start Refutation
% 0.82/1.05  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.82/1.05  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.82/1.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.82/1.05  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.82/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.05  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.82/1.05  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.82/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.05  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.82/1.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.82/1.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.82/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.05  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.82/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.05  thf(t138_zfmisc_1, conjecture,
% 0.82/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.05     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.82/1.05       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.05         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.82/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.05    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.05        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.82/1.05          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.05            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.82/1.05    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.82/1.05  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf(d2_zfmisc_1, axiom,
% 0.82/1.05    (![A:$i,B:$i,C:$i]:
% 0.82/1.05     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.82/1.05       ( ![D:$i]:
% 0.82/1.05         ( ( r2_hidden @ D @ C ) <=>
% 0.82/1.05           ( ?[E:$i,F:$i]:
% 0.82/1.05             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.82/1.05               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.82/1.05  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.82/1.05  thf(zf_stmt_2, axiom,
% 0.82/1.05    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.82/1.05     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.82/1.05       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.82/1.05         ( r2_hidden @ E @ A ) ) ))).
% 0.82/1.05  thf(zf_stmt_3, axiom,
% 0.82/1.05    (![A:$i,B:$i,C:$i]:
% 0.82/1.05     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.82/1.05       ( ![D:$i]:
% 0.82/1.05         ( ( r2_hidden @ D @ C ) <=>
% 0.82/1.05           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.82/1.05  thf('1', plain,
% 0.82/1.05      (![X21 : $i, X22 : $i, X25 : $i]:
% 0.82/1.05         (((X25) = (k2_zfmisc_1 @ X22 @ X21))
% 0.82/1.05          | (zip_tseitin_0 @ (sk_F @ X25 @ X21 @ X22) @ 
% 0.82/1.05             (sk_E @ X25 @ X21 @ X22) @ (sk_D @ X25 @ X21 @ X22) @ X21 @ X22)
% 0.82/1.05          | (r2_hidden @ (sk_D @ X25 @ X21 @ X22) @ X25))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.05  thf('2', plain,
% 0.82/1.05      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.82/1.05         ((r2_hidden @ X13 @ X15)
% 0.82/1.05          | ~ (zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.05  thf('3', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.05         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.82/1.05          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.82/1.05          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.82/1.05      inference('sup-', [status(thm)], ['1', '2'])).
% 0.82/1.05  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.82/1.05  thf('4', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.82/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.82/1.05  thf(t28_xboole_1, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.82/1.05  thf('5', plain,
% 0.82/1.05      (![X8 : $i, X9 : $i]:
% 0.82/1.05         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.82/1.05      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.82/1.05  thf('6', plain,
% 0.82/1.05      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.82/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.82/1.05  thf(t4_xboole_0, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.82/1.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.82/1.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.82/1.05            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.82/1.05  thf('7', plain,
% 0.82/1.05      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.82/1.05         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.82/1.05          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.82/1.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.82/1.05  thf('8', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.05      inference('sup-', [status(thm)], ['6', '7'])).
% 0.82/1.05  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.82/1.05  thf('9', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.82/1.05      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.82/1.05  thf('10', plain,
% 0.82/1.05      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.82/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.82/1.05  thf('11', plain,
% 0.82/1.05      (![X4 : $i, X5 : $i]:
% 0.82/1.05         ((r1_xboole_0 @ X4 @ X5)
% 0.82/1.05          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.82/1.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.82/1.05  thf('12', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.82/1.05          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.05      inference('sup+', [status(thm)], ['10', '11'])).
% 0.82/1.05  thf('13', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.82/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.82/1.05  thf(d3_tarski, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( r1_tarski @ A @ B ) <=>
% 0.82/1.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.82/1.05  thf('14', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.05         (~ (r2_hidden @ X0 @ X1)
% 0.82/1.05          | (r2_hidden @ X0 @ X2)
% 0.82/1.05          | ~ (r1_tarski @ X1 @ X2))),
% 0.82/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.05  thf('15', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.82/1.05      inference('sup-', [status(thm)], ['13', '14'])).
% 0.82/1.05  thf('16', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.82/1.05          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.82/1.05      inference('sup-', [status(thm)], ['12', '15'])).
% 0.82/1.05  thf('17', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.05      inference('sup-', [status(thm)], ['6', '7'])).
% 0.82/1.05  thf('18', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.82/1.05      inference('sup-', [status(thm)], ['16', '17'])).
% 0.82/1.05  thf('19', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.82/1.05      inference('sup-', [status(thm)], ['9', '18'])).
% 0.82/1.05  thf('20', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.82/1.05      inference('demod', [status(thm)], ['8', '19'])).
% 0.82/1.05  thf('21', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.82/1.05          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.82/1.05      inference('sup-', [status(thm)], ['3', '20'])).
% 0.82/1.05  thf(t113_zfmisc_1, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.82/1.05       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.82/1.05  thf('22', plain,
% 0.82/1.05      (![X34 : $i, X35 : $i]:
% 0.82/1.05         (((k2_zfmisc_1 @ X34 @ X35) = (k1_xboole_0))
% 0.82/1.05          | ((X35) != (k1_xboole_0)))),
% 0.82/1.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.82/1.05  thf('23', plain,
% 0.82/1.05      (![X34 : $i]: ((k2_zfmisc_1 @ X34 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.05      inference('simplify', [status(thm)], ['22'])).
% 0.82/1.05  thf('24', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         (((X1) = (k1_xboole_0))
% 0.82/1.05          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.82/1.05      inference('demod', [status(thm)], ['21', '23'])).
% 0.82/1.05  thf('25', plain,
% 0.82/1.05      (![X1 : $i, X3 : $i]:
% 0.82/1.05         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.82/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.05  thf(l54_zfmisc_1, axiom,
% 0.82/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.05     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.82/1.05       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.82/1.05  thf('26', plain,
% 0.82/1.05      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i]:
% 0.82/1.05         ((r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X32))
% 0.82/1.05          | ~ (r2_hidden @ X30 @ X32)
% 0.82/1.05          | ~ (r2_hidden @ X28 @ X29))),
% 0.82/1.05      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.82/1.05  thf('27', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.05         ((r1_tarski @ X0 @ X1)
% 0.82/1.05          | ~ (r2_hidden @ X3 @ X2)
% 0.82/1.05          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.82/1.05             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['25', '26'])).
% 0.82/1.05  thf('28', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.05         (((X0) = (k1_xboole_0))
% 0.82/1.05          | (r2_hidden @ 
% 0.82/1.05             (k4_tarski @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ (sk_C @ X3 @ X2)) @ 
% 0.82/1.05             (k2_zfmisc_1 @ X0 @ X2))
% 0.82/1.05          | (r1_tarski @ X2 @ X3))),
% 0.82/1.05      inference('sup-', [status(thm)], ['24', '27'])).
% 0.82/1.05  thf('29', plain,
% 0.82/1.05      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.82/1.05        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('30', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.05         (~ (r2_hidden @ X0 @ X1)
% 0.82/1.05          | (r2_hidden @ X0 @ X2)
% 0.82/1.05          | ~ (r1_tarski @ X1 @ X2))),
% 0.82/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.05  thf('31', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.82/1.05          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['29', '30'])).
% 0.82/1.05  thf('32', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         ((r1_tarski @ sk_B @ X0)
% 0.82/1.05          | ((sk_A) = (k1_xboole_0))
% 0.82/1.05          | (r2_hidden @ 
% 0.82/1.05             (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ (sk_C @ X0 @ sk_B)) @ 
% 0.82/1.05             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['28', '31'])).
% 0.82/1.05  thf('33', plain,
% 0.82/1.05      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.82/1.05         ((r2_hidden @ X30 @ X31)
% 0.82/1.05          | ~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X31)))),
% 0.82/1.05      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.82/1.05  thf('34', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         (((sk_A) = (k1_xboole_0))
% 0.82/1.05          | (r1_tarski @ sk_B @ X0)
% 0.82/1.05          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_D_1))),
% 0.82/1.05      inference('sup-', [status(thm)], ['32', '33'])).
% 0.82/1.05  thf('35', plain,
% 0.82/1.05      (![X1 : $i, X3 : $i]:
% 0.82/1.05         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.82/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.05  thf('36', plain,
% 0.82/1.05      (((r1_tarski @ sk_B @ sk_D_1)
% 0.82/1.05        | ((sk_A) = (k1_xboole_0))
% 0.82/1.05        | (r1_tarski @ sk_B @ sk_D_1))),
% 0.82/1.05      inference('sup-', [status(thm)], ['34', '35'])).
% 0.82/1.05  thf('37', plain, ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_D_1))),
% 0.82/1.05      inference('simplify', [status(thm)], ['36'])).
% 0.82/1.05  thf('38', plain,
% 0.82/1.05      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('39', plain,
% 0.82/1.05      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.82/1.05      inference('split', [status(esa)], ['38'])).
% 0.82/1.05  thf('40', plain,
% 0.82/1.05      (![X1 : $i, X3 : $i]:
% 0.82/1.05         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.82/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.05  thf('41', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         (((X1) = (k1_xboole_0))
% 0.82/1.05          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.82/1.05      inference('demod', [status(thm)], ['21', '23'])).
% 0.82/1.05  thf('42', plain,
% 0.82/1.05      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i]:
% 0.82/1.05         ((r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X32))
% 0.82/1.05          | ~ (r2_hidden @ X30 @ X32)
% 0.82/1.05          | ~ (r2_hidden @ X28 @ X29))),
% 0.82/1.05      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.82/1.05  thf('43', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.05         (((X0) = (k1_xboole_0))
% 0.82/1.05          | ~ (r2_hidden @ X3 @ X2)
% 0.82/1.05          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ 
% 0.82/1.05             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['41', '42'])).
% 0.82/1.05  thf('44', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.05         ((r1_tarski @ X0 @ X1)
% 0.82/1.05          | (r2_hidden @ 
% 0.82/1.05             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 0.82/1.05             (k2_zfmisc_1 @ X0 @ X2))
% 0.82/1.05          | ((X2) = (k1_xboole_0)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['40', '43'])).
% 0.82/1.05  thf('45', plain,
% 0.82/1.05      (![X0 : $i]:
% 0.82/1.05         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.82/1.05          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['29', '30'])).
% 0.82/1.05  thf('46', plain,
% 0.82/1.05      (![X0 : $i, X1 : $i]:
% 0.82/1.05         (((sk_B) = (k1_xboole_0))
% 0.82/1.05          | (r1_tarski @ sk_A @ X1)
% 0.82/1.05          | (r2_hidden @ 
% 0.82/1.05             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 0.82/1.05             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['44', '45'])).
% 0.82/1.05  thf('47', plain,
% 0.82/1.05      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.82/1.05         ((r2_hidden @ X28 @ X29)
% 0.82/1.05          | ~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X31)))),
% 0.82/1.05      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.82/1.05  thf('48', plain,
% 0.82/1.05      (![X1 : $i]:
% 0.82/1.05         ((r1_tarski @ sk_A @ X1)
% 0.82/1.05          | ((sk_B) = (k1_xboole_0))
% 0.82/1.05          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_C_2))),
% 0.82/1.05      inference('sup-', [status(thm)], ['46', '47'])).
% 0.82/1.05  thf('49', plain,
% 0.82/1.05      (![X1 : $i, X3 : $i]:
% 0.82/1.05         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.82/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.05  thf('50', plain,
% 0.82/1.05      ((((sk_B) = (k1_xboole_0))
% 0.82/1.05        | (r1_tarski @ sk_A @ sk_C_2)
% 0.82/1.05        | (r1_tarski @ sk_A @ sk_C_2))),
% 0.82/1.05      inference('sup-', [status(thm)], ['48', '49'])).
% 0.82/1.05  thf('51', plain, (((r1_tarski @ sk_A @ sk_C_2) | ((sk_B) = (k1_xboole_0)))),
% 0.82/1.05      inference('simplify', [status(thm)], ['50'])).
% 0.82/1.05  thf('52', plain,
% 0.82/1.05      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.82/1.05      inference('split', [status(esa)], ['38'])).
% 0.82/1.05  thf('53', plain,
% 0.82/1.05      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['51', '52'])).
% 0.82/1.05  thf('54', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('55', plain,
% 0.82/1.05      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.82/1.05         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.82/1.05      inference('sup-', [status(thm)], ['53', '54'])).
% 0.82/1.05  thf('56', plain,
% 0.82/1.05      (![X34 : $i]: ((k2_zfmisc_1 @ X34 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.05      inference('simplify', [status(thm)], ['22'])).
% 0.82/1.05  thf('57', plain,
% 0.82/1.05      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.82/1.05      inference('demod', [status(thm)], ['55', '56'])).
% 0.82/1.05  thf('58', plain, (((r1_tarski @ sk_A @ sk_C_2))),
% 0.82/1.05      inference('simplify', [status(thm)], ['57'])).
% 0.82/1.05  thf('59', plain,
% 0.82/1.05      (~ ((r1_tarski @ sk_B @ sk_D_1)) | ~ ((r1_tarski @ sk_A @ sk_C_2))),
% 0.82/1.05      inference('split', [status(esa)], ['38'])).
% 0.82/1.05  thf('60', plain, (~ ((r1_tarski @ sk_B @ sk_D_1))),
% 0.82/1.05      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.82/1.05  thf('61', plain, (~ (r1_tarski @ sk_B @ sk_D_1)),
% 0.82/1.05      inference('simpl_trail', [status(thm)], ['39', '60'])).
% 0.82/1.05  thf('62', plain, (((sk_A) = (k1_xboole_0))),
% 0.82/1.05      inference('clc', [status(thm)], ['37', '61'])).
% 0.82/1.05  thf('63', plain,
% 0.82/1.05      (![X34 : $i, X35 : $i]:
% 0.82/1.05         (((k2_zfmisc_1 @ X34 @ X35) = (k1_xboole_0))
% 0.82/1.05          | ((X34) != (k1_xboole_0)))),
% 0.82/1.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.82/1.05  thf('64', plain,
% 0.82/1.05      (![X35 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X35) = (k1_xboole_0))),
% 0.82/1.05      inference('simplify', [status(thm)], ['63'])).
% 0.82/1.05  thf('65', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.82/1.05      inference('demod', [status(thm)], ['0', '62', '64'])).
% 0.82/1.05  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 0.82/1.05  
% 0.82/1.05  % SZS output end Refutation
% 0.82/1.05  
% 0.82/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
