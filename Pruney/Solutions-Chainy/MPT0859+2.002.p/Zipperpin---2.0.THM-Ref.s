%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dDMfDd9lel

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:48 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 503 expanded)
%              Number of leaves         :   29 ( 157 expanded)
%              Depth                    :   21
%              Number of atoms          : 1154 (4933 expanded)
%              Number of equality atoms :   71 ( 298 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t15_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_mcart_1])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ( r2_hidden @ X33 @ X32 )
      | ( X32
        = ( k4_xboole_0 @ X32 @ ( k2_tarski @ X31 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ( r2_hidden @ X33 @ X32 )
      | ( X32
        = ( k4_xboole_0 @ X32 @ ( k2_tarski @ X31 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('26',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X36 @ X35 )
      | ~ ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('33',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_C ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('53',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('55',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('57',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_2 ) ),
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

thf('59',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X27 @ X24 @ X25 ) @ ( sk_E_1 @ X27 @ X24 @ X25 ) @ X27 @ X24 @ X25 )
      | ( X26
       != ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X27 @ X24 @ X25 ) @ ( sk_E_1 @ X27 @ X24 @ X25 ) @ X27 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) @ ( sk_E_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17
        = ( k4_tarski @ X15 @ X16 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('63',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) @ ( sk_F_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) @ ( sk_F_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('65',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X44 @ X45 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('66',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_E_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_F_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_F_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('69',plain,(
    ! [X44: $i,X46: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X44 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('70',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_F_1 @ sk_A @ sk_D_2 @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('74',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X38 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('76',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X20 )
      | ~ ( r2_hidden @ X15 @ X20 )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ( X17
       != ( k4_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    ! [X15: $i,X16: $i,X18: $i,X20: $i] :
      ( ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X15 @ X20 )
      | ( zip_tseitin_0 @ X16 @ X15 @ ( k4_tarski @ X15 @ X16 ) @ X18 @ X20 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_mcart_1 @ sk_A ) @ X1 @ ( k4_tarski @ X1 @ ( k2_mcart_1 @ sk_A ) ) @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k2_mcart_1 @ sk_A ) @ X1 @ ( k4_tarski @ X1 @ ( k2_mcart_1 @ sk_A ) ) @ sk_D_2 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X23 @ X26 )
      | ( X26
       != ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('82',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ ( k2_zfmisc_1 @ X25 @ X24 ) )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ ( k2_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X0 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ ( k2_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X0 ) @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['72','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['71','84'])).

thf('86',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_2 ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','85'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('87',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_mcart_1 @ X42 )
        = X41 )
      | ~ ( r2_hidden @ X42 @ ( k2_zfmisc_1 @ ( k1_tarski @ X41 ) @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('88',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('92',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['89'])).

thf('96',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['90','96'])).

thf('98',plain,
    ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['88','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_A ) ) @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['71','84'])).

thf('100',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_mcart_1 @ X42 )
        = X41 )
      | ~ ( r2_hidden @ X42 @ ( k2_zfmisc_1 @ ( k1_tarski @ X41 ) @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('102',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['92'])).

thf('104',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['92'])).

thf('105',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['94','104'])).

thf('106',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['103','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dDMfDd9lel
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.25/1.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.25/1.46  % Solved by: fo/fo7.sh
% 1.25/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.25/1.46  % done 1435 iterations in 1.002s
% 1.25/1.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.25/1.46  % SZS output start Refutation
% 1.25/1.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.25/1.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.25/1.46  thf(sk_C_type, type, sk_C: $i).
% 1.25/1.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.25/1.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.25/1.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.25/1.46  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.25/1.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 1.25/1.46  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 1.25/1.46  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.25/1.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.25/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.25/1.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.25/1.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.25/1.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.25/1.46  thf(sk_B_type, type, sk_B: $i).
% 1.25/1.46  thf(t69_enumset1, axiom,
% 1.25/1.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.25/1.46  thf('0', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.25/1.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.25/1.46  thf(d10_xboole_0, axiom,
% 1.25/1.46    (![A:$i,B:$i]:
% 1.25/1.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.25/1.46  thf('1', plain,
% 1.25/1.46      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.25/1.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.25/1.46  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.25/1.46      inference('simplify', [status(thm)], ['1'])).
% 1.25/1.46  thf(t38_zfmisc_1, axiom,
% 1.25/1.46    (![A:$i,B:$i,C:$i]:
% 1.25/1.46     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.25/1.46       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.25/1.46  thf('3', plain,
% 1.25/1.46      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.25/1.46         ((r2_hidden @ X34 @ X35)
% 1.25/1.46          | ~ (r1_tarski @ (k2_tarski @ X34 @ X36) @ X35))),
% 1.25/1.46      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.25/1.46  thf('4', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['2', '3'])).
% 1.25/1.46  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.25/1.46      inference('sup+', [status(thm)], ['0', '4'])).
% 1.25/1.46  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.25/1.46      inference('sup+', [status(thm)], ['0', '4'])).
% 1.25/1.46  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.25/1.46      inference('sup+', [status(thm)], ['0', '4'])).
% 1.25/1.46  thf(t15_mcart_1, conjecture,
% 1.25/1.46    (![A:$i,B:$i,C:$i,D:$i]:
% 1.25/1.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 1.25/1.46       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 1.25/1.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 1.25/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.25/1.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.25/1.46        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 1.25/1.46          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 1.25/1.46            ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )),
% 1.25/1.46    inference('cnf.neg', [status(esa)], [t15_mcart_1])).
% 1.25/1.46  thf('8', plain,
% 1.25/1.46      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_2))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.46  thf(t10_mcart_1, axiom,
% 1.25/1.46    (![A:$i,B:$i,C:$i]:
% 1.25/1.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.25/1.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.25/1.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.25/1.46  thf('9', plain,
% 1.25/1.46      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.25/1.46         ((r2_hidden @ (k1_mcart_1 @ X38) @ X39)
% 1.25/1.46          | ~ (r2_hidden @ X38 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 1.25/1.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.25/1.46  thf('10', plain,
% 1.25/1.46      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 1.25/1.46      inference('sup-', [status(thm)], ['8', '9'])).
% 1.25/1.46  thf(t144_zfmisc_1, axiom,
% 1.25/1.46    (![A:$i,B:$i,C:$i]:
% 1.25/1.46     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.25/1.46          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.25/1.46  thf('11', plain,
% 1.25/1.46      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.25/1.46         ((r2_hidden @ X31 @ X32)
% 1.25/1.46          | (r2_hidden @ X33 @ X32)
% 1.25/1.46          | ((X32) = (k4_xboole_0 @ X32 @ (k2_tarski @ X31 @ X33))))),
% 1.25/1.46      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.25/1.46  thf(d5_xboole_0, axiom,
% 1.25/1.46    (![A:$i,B:$i,C:$i]:
% 1.25/1.46     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.25/1.46       ( ![D:$i]:
% 1.25/1.46         ( ( r2_hidden @ D @ C ) <=>
% 1.25/1.46           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.25/1.46  thf('12', plain,
% 1.25/1.46      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X4 @ X3)
% 1.25/1.46          | ~ (r2_hidden @ X4 @ X2)
% 1.25/1.46          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.25/1.46      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.25/1.46  thf('13', plain,
% 1.25/1.46      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X4 @ X2)
% 1.25/1.46          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.25/1.46      inference('simplify', [status(thm)], ['12'])).
% 1.25/1.46  thf('14', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X3 @ X0)
% 1.25/1.46          | (r2_hidden @ X1 @ X0)
% 1.25/1.46          | (r2_hidden @ X2 @ X0)
% 1.25/1.46          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['11', '13'])).
% 1.25/1.46  thf('15', plain,
% 1.25/1.46      (![X0 : $i]:
% 1.25/1.46         ((r2_hidden @ sk_B @ X0)
% 1.25/1.46          | (r2_hidden @ sk_C @ X0)
% 1.25/1.46          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['10', '14'])).
% 1.25/1.46  thf('16', plain,
% 1.25/1.46      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.25/1.46        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.25/1.46      inference('sup-', [status(thm)], ['7', '15'])).
% 1.25/1.46  thf('17', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.25/1.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.25/1.46  thf('18', plain,
% 1.25/1.46      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.25/1.46         ((r2_hidden @ X31 @ X32)
% 1.25/1.46          | (r2_hidden @ X33 @ X32)
% 1.25/1.46          | ((X32) = (k4_xboole_0 @ X32 @ (k2_tarski @ X31 @ X33))))),
% 1.25/1.46      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.25/1.46  thf('19', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.25/1.46          | (r2_hidden @ X0 @ X1)
% 1.25/1.46          | (r2_hidden @ X0 @ X1))),
% 1.25/1.46      inference('sup+', [status(thm)], ['17', '18'])).
% 1.25/1.46  thf('20', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         ((r2_hidden @ X0 @ X1)
% 1.25/1.46          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.25/1.46      inference('simplify', [status(thm)], ['19'])).
% 1.25/1.46  thf('21', plain,
% 1.25/1.46      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X4 @ X2)
% 1.25/1.46          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.25/1.46      inference('simplify', [status(thm)], ['12'])).
% 1.25/1.46  thf('22', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X2 @ X0)
% 1.25/1.46          | (r2_hidden @ X1 @ X0)
% 1.25/1.46          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['20', '21'])).
% 1.25/1.46  thf('23', plain,
% 1.25/1.46      (![X0 : $i]:
% 1.25/1.46         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.25/1.46          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 1.25/1.46          | ~ (r2_hidden @ sk_C @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['16', '22'])).
% 1.25/1.46  thf('24', plain,
% 1.25/1.46      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 1.25/1.46        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 1.25/1.46      inference('sup-', [status(thm)], ['6', '23'])).
% 1.25/1.46  thf('25', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.25/1.46      inference('sup+', [status(thm)], ['0', '4'])).
% 1.25/1.46  thf('26', plain,
% 1.25/1.46      (![X34 : $i, X36 : $i, X37 : $i]:
% 1.25/1.46         ((r1_tarski @ (k2_tarski @ X34 @ X36) @ X37)
% 1.25/1.46          | ~ (r2_hidden @ X36 @ X37)
% 1.25/1.46          | ~ (r2_hidden @ X34 @ X37))),
% 1.25/1.46      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.25/1.46  thf('27', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.25/1.46          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['25', '26'])).
% 1.25/1.46  thf('28', plain,
% 1.25/1.46      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.25/1.46        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_C) @ 
% 1.25/1.46           (k1_tarski @ sk_C)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['24', '27'])).
% 1.25/1.46  thf('29', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.25/1.46      inference('simplify', [status(thm)], ['1'])).
% 1.25/1.46  thf('30', plain,
% 1.25/1.46      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.25/1.46         ((r2_hidden @ X36 @ X35)
% 1.25/1.46          | ~ (r1_tarski @ (k2_tarski @ X34 @ X36) @ X35))),
% 1.25/1.46      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.25/1.46  thf('31', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['29', '30'])).
% 1.25/1.46  thf('32', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['2', '3'])).
% 1.25/1.46  thf('33', plain,
% 1.25/1.46      (![X34 : $i, X36 : $i, X37 : $i]:
% 1.25/1.46         ((r1_tarski @ (k2_tarski @ X34 @ X36) @ X37)
% 1.25/1.46          | ~ (r2_hidden @ X36 @ X37)
% 1.25/1.46          | ~ (r2_hidden @ X34 @ X37))),
% 1.25/1.46      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.25/1.46  thf('34', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.25/1.46          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['32', '33'])).
% 1.25/1.46  thf('35', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['31', '34'])).
% 1.25/1.46  thf('36', plain,
% 1.25/1.46      (![X6 : $i, X8 : $i]:
% 1.25/1.46         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.25/1.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.25/1.46  thf('37', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 1.25/1.46          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['35', '36'])).
% 1.25/1.46  thf('38', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['31', '34'])).
% 1.25/1.46  thf('39', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.25/1.46      inference('demod', [status(thm)], ['37', '38'])).
% 1.25/1.46  thf('40', plain,
% 1.25/1.46      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.25/1.46        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 1.25/1.46           (k1_tarski @ sk_C)))),
% 1.25/1.46      inference('demod', [status(thm)], ['28', '39'])).
% 1.25/1.46  thf('41', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.25/1.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.25/1.46  thf('42', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['2', '3'])).
% 1.25/1.46  thf('43', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.25/1.46          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['32', '33'])).
% 1.25/1.46  thf('44', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['42', '43'])).
% 1.25/1.46  thf('45', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 1.25/1.46      inference('sup+', [status(thm)], ['41', '44'])).
% 1.25/1.46  thf('46', plain,
% 1.25/1.46      (![X6 : $i, X8 : $i]:
% 1.25/1.46         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.25/1.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.25/1.46  thf('47', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.25/1.46          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['45', '46'])).
% 1.25/1.46  thf('48', plain,
% 1.25/1.46      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 1.25/1.46        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['40', '47'])).
% 1.25/1.46  thf('49', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X2 @ X0)
% 1.25/1.46          | (r2_hidden @ X1 @ X0)
% 1.25/1.46          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['20', '21'])).
% 1.25/1.46  thf('50', plain,
% 1.25/1.46      (![X0 : $i]:
% 1.25/1.46         (((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.25/1.46          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 1.25/1.46          | ~ (r2_hidden @ sk_B @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['48', '49'])).
% 1.25/1.46  thf('51', plain,
% 1.25/1.46      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 1.25/1.46        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['5', '50'])).
% 1.25/1.46  thf('52', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.25/1.46          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['25', '26'])).
% 1.25/1.46  thf('53', plain,
% 1.25/1.46      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.25/1.46        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_B) @ 
% 1.25/1.46           (k1_tarski @ sk_B)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['51', '52'])).
% 1.25/1.46  thf('54', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.25/1.46      inference('demod', [status(thm)], ['37', '38'])).
% 1.25/1.46  thf('55', plain,
% 1.25/1.46      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.25/1.46        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 1.25/1.46           (k1_tarski @ sk_B)))),
% 1.25/1.46      inference('demod', [status(thm)], ['53', '54'])).
% 1.25/1.46  thf('56', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.25/1.46          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['45', '46'])).
% 1.25/1.46  thf('57', plain,
% 1.25/1.46      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 1.25/1.46        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['55', '56'])).
% 1.25/1.46  thf('58', plain,
% 1.25/1.46      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_2))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.46  thf(d2_zfmisc_1, axiom,
% 1.25/1.46    (![A:$i,B:$i,C:$i]:
% 1.25/1.46     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.25/1.46       ( ![D:$i]:
% 1.25/1.46         ( ( r2_hidden @ D @ C ) <=>
% 1.25/1.46           ( ?[E:$i,F:$i]:
% 1.25/1.46             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 1.25/1.46               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 1.25/1.46  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 1.25/1.46  thf(zf_stmt_2, axiom,
% 1.25/1.46    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 1.25/1.46     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 1.25/1.46       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 1.25/1.46         ( r2_hidden @ E @ A ) ) ))).
% 1.25/1.46  thf(zf_stmt_3, axiom,
% 1.25/1.46    (![A:$i,B:$i,C:$i]:
% 1.25/1.46     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.25/1.46       ( ![D:$i]:
% 1.25/1.46         ( ( r2_hidden @ D @ C ) <=>
% 1.25/1.46           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 1.25/1.46  thf('59', plain,
% 1.25/1.46      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X27 @ X26)
% 1.25/1.46          | (zip_tseitin_0 @ (sk_F_1 @ X27 @ X24 @ X25) @ 
% 1.25/1.46             (sk_E_1 @ X27 @ X24 @ X25) @ X27 @ X24 @ X25)
% 1.25/1.46          | ((X26) != (k2_zfmisc_1 @ X25 @ X24)))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.25/1.46  thf('60', plain,
% 1.25/1.46      (![X24 : $i, X25 : $i, X27 : $i]:
% 1.25/1.46         ((zip_tseitin_0 @ (sk_F_1 @ X27 @ X24 @ X25) @ 
% 1.25/1.46           (sk_E_1 @ X27 @ X24 @ X25) @ X27 @ X24 @ X25)
% 1.25/1.46          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X25 @ X24)))),
% 1.25/1.46      inference('simplify', [status(thm)], ['59'])).
% 1.25/1.46  thf('61', plain,
% 1.25/1.46      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C)) @ 
% 1.25/1.46        (sk_E_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A @ sk_D_2 @ 
% 1.25/1.46        (k2_tarski @ sk_B @ sk_C))),
% 1.25/1.46      inference('sup-', [status(thm)], ['58', '60'])).
% 1.25/1.46  thf('62', plain,
% 1.25/1.46      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.25/1.46         (((X17) = (k4_tarski @ X15 @ X16))
% 1.25/1.46          | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X19))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.25/1.46  thf('63', plain,
% 1.25/1.46      (((sk_A)
% 1.25/1.46         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C)) @ 
% 1.25/1.46            (sk_F_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C))))),
% 1.25/1.46      inference('sup-', [status(thm)], ['61', '62'])).
% 1.25/1.46  thf('64', plain,
% 1.25/1.46      (((sk_A)
% 1.25/1.46         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C)) @ 
% 1.25/1.46            (sk_F_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C))))),
% 1.25/1.46      inference('sup-', [status(thm)], ['61', '62'])).
% 1.25/1.46  thf(t7_mcart_1, axiom,
% 1.25/1.46    (![A:$i,B:$i]:
% 1.25/1.46     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 1.25/1.46       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 1.25/1.46  thf('65', plain,
% 1.25/1.46      (![X44 : $i, X45 : $i]: ((k1_mcart_1 @ (k4_tarski @ X44 @ X45)) = (X44))),
% 1.25/1.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.25/1.46  thf('66', plain,
% 1.25/1.46      (((k1_mcart_1 @ sk_A)
% 1.25/1.46         = (sk_E_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C)))),
% 1.25/1.46      inference('sup+', [status(thm)], ['64', '65'])).
% 1.25/1.46  thf('67', plain,
% 1.25/1.46      (((sk_A)
% 1.25/1.46         = (k4_tarski @ (k1_mcart_1 @ sk_A) @ 
% 1.25/1.46            (sk_F_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C))))),
% 1.25/1.46      inference('demod', [status(thm)], ['63', '66'])).
% 1.25/1.46  thf('68', plain,
% 1.25/1.46      (((sk_A)
% 1.25/1.46         = (k4_tarski @ (k1_mcart_1 @ sk_A) @ 
% 1.25/1.46            (sk_F_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C))))),
% 1.25/1.46      inference('demod', [status(thm)], ['63', '66'])).
% 1.25/1.46  thf('69', plain,
% 1.25/1.46      (![X44 : $i, X46 : $i]: ((k2_mcart_1 @ (k4_tarski @ X44 @ X46)) = (X46))),
% 1.25/1.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.25/1.46  thf('70', plain,
% 1.25/1.46      (((k2_mcart_1 @ sk_A)
% 1.25/1.46         = (sk_F_1 @ sk_A @ sk_D_2 @ (k2_tarski @ sk_B @ sk_C)))),
% 1.25/1.46      inference('sup+', [status(thm)], ['68', '69'])).
% 1.25/1.46  thf('71', plain,
% 1.25/1.46      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 1.25/1.46      inference('demod', [status(thm)], ['67', '70'])).
% 1.25/1.46  thf('72', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.25/1.46      inference('demod', [status(thm)], ['37', '38'])).
% 1.25/1.46  thf('73', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['2', '3'])).
% 1.25/1.46  thf('74', plain,
% 1.25/1.46      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_2))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.46  thf('75', plain,
% 1.25/1.46      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.25/1.46         ((r2_hidden @ (k2_mcart_1 @ X38) @ X40)
% 1.25/1.46          | ~ (r2_hidden @ X38 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 1.25/1.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.25/1.46  thf('76', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2)),
% 1.25/1.46      inference('sup-', [status(thm)], ['74', '75'])).
% 1.25/1.46  thf('77', plain,
% 1.25/1.46      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 1.25/1.46         ((zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X20)
% 1.25/1.46          | ~ (r2_hidden @ X15 @ X20)
% 1.25/1.46          | ~ (r2_hidden @ X16 @ X18)
% 1.25/1.46          | ((X17) != (k4_tarski @ X15 @ X16)))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.25/1.46  thf('78', plain,
% 1.25/1.46      (![X15 : $i, X16 : $i, X18 : $i, X20 : $i]:
% 1.25/1.46         (~ (r2_hidden @ X16 @ X18)
% 1.25/1.46          | ~ (r2_hidden @ X15 @ X20)
% 1.25/1.46          | (zip_tseitin_0 @ X16 @ X15 @ (k4_tarski @ X15 @ X16) @ X18 @ X20))),
% 1.25/1.46      inference('simplify', [status(thm)], ['77'])).
% 1.25/1.46  thf('79', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         ((zip_tseitin_0 @ (k2_mcart_1 @ sk_A) @ X1 @ 
% 1.25/1.46           (k4_tarski @ X1 @ (k2_mcart_1 @ sk_A)) @ sk_D_2 @ X0)
% 1.25/1.46          | ~ (r2_hidden @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['76', '78'])).
% 1.25/1.46  thf('80', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (zip_tseitin_0 @ (k2_mcart_1 @ sk_A) @ X1 @ 
% 1.25/1.46          (k4_tarski @ X1 @ (k2_mcart_1 @ sk_A)) @ sk_D_2 @ 
% 1.25/1.46          (k2_tarski @ X1 @ X0))),
% 1.25/1.46      inference('sup-', [status(thm)], ['73', '79'])).
% 1.25/1.46  thf('81', plain,
% 1.25/1.46      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.25/1.46         (~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 @ X25)
% 1.25/1.46          | (r2_hidden @ X23 @ X26)
% 1.25/1.46          | ((X26) != (k2_zfmisc_1 @ X25 @ X24)))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.25/1.46  thf('82', plain,
% 1.25/1.46      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.25/1.46         ((r2_hidden @ X23 @ (k2_zfmisc_1 @ X25 @ X24))
% 1.25/1.46          | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 @ X25))),
% 1.25/1.46      inference('simplify', [status(thm)], ['81'])).
% 1.25/1.46  thf('83', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (r2_hidden @ (k4_tarski @ X1 @ (k2_mcart_1 @ sk_A)) @ 
% 1.25/1.46          (k2_zfmisc_1 @ (k2_tarski @ X1 @ X0) @ sk_D_2))),
% 1.25/1.46      inference('sup-', [status(thm)], ['80', '82'])).
% 1.25/1.46  thf('84', plain,
% 1.25/1.46      (![X0 : $i, X1 : $i]:
% 1.25/1.46         (r2_hidden @ (k4_tarski @ X0 @ (k2_mcart_1 @ sk_A)) @ 
% 1.25/1.46          (k2_zfmisc_1 @ (k2_tarski @ X1 @ X0) @ sk_D_2))),
% 1.25/1.46      inference('sup+', [status(thm)], ['72', '83'])).
% 1.25/1.46  thf('85', plain,
% 1.25/1.46      (![X0 : $i]:
% 1.25/1.46         (r2_hidden @ sk_A @ 
% 1.25/1.46          (k2_zfmisc_1 @ (k2_tarski @ X0 @ (k1_mcart_1 @ sk_A)) @ sk_D_2))),
% 1.25/1.46      inference('sup+', [status(thm)], ['71', '84'])).
% 1.25/1.46  thf('86', plain,
% 1.25/1.46      (((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_2))
% 1.25/1.46        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 1.25/1.46      inference('sup+', [status(thm)], ['57', '85'])).
% 1.25/1.46  thf(t12_mcart_1, axiom,
% 1.25/1.46    (![A:$i,B:$i,C:$i]:
% 1.25/1.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 1.25/1.46       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 1.25/1.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.25/1.46  thf('87', plain,
% 1.25/1.46      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.25/1.46         (((k1_mcart_1 @ X42) = (X41))
% 1.25/1.46          | ~ (r2_hidden @ X42 @ (k2_zfmisc_1 @ (k1_tarski @ X41) @ X43)))),
% 1.25/1.46      inference('cnf', [status(esa)], [t12_mcart_1])).
% 1.25/1.46  thf('88', plain,
% 1.25/1.46      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 1.25/1.46        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 1.25/1.46      inference('sup-', [status(thm)], ['86', '87'])).
% 1.25/1.46  thf('89', plain,
% 1.25/1.46      ((((k1_mcart_1 @ sk_A) != (sk_C))
% 1.25/1.46        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.46  thf('90', plain,
% 1.25/1.46      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 1.25/1.46         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 1.25/1.46      inference('split', [status(esa)], ['89'])).
% 1.25/1.46  thf('91', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2)),
% 1.25/1.46      inference('sup-', [status(thm)], ['74', '75'])).
% 1.25/1.46  thf('92', plain,
% 1.25/1.46      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 1.25/1.46        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 1.25/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.46  thf('93', plain,
% 1.25/1.46      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))
% 1.25/1.46         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2)))),
% 1.25/1.46      inference('split', [status(esa)], ['92'])).
% 1.25/1.46  thf('94', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 1.25/1.46      inference('sup-', [status(thm)], ['91', '93'])).
% 1.25/1.46  thf('95', plain,
% 1.25/1.46      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 1.25/1.46       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 1.25/1.46      inference('split', [status(esa)], ['89'])).
% 1.25/1.46  thf('96', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 1.25/1.46      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 1.25/1.46  thf('97', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 1.25/1.46      inference('simpl_trail', [status(thm)], ['90', '96'])).
% 1.25/1.46  thf('98', plain,
% 1.25/1.46      (((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))),
% 1.25/1.46      inference('simplify_reflect-', [status(thm)], ['88', '97'])).
% 1.25/1.46  thf('99', plain,
% 1.25/1.46      (![X0 : $i]:
% 1.25/1.46         (r2_hidden @ sk_A @ 
% 1.25/1.46          (k2_zfmisc_1 @ (k2_tarski @ X0 @ (k1_mcart_1 @ sk_A)) @ sk_D_2))),
% 1.25/1.46      inference('sup+', [status(thm)], ['71', '84'])).
% 1.25/1.46  thf('100', plain,
% 1.25/1.46      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D_2))),
% 1.25/1.46      inference('sup+', [status(thm)], ['98', '99'])).
% 1.25/1.46  thf('101', plain,
% 1.25/1.46      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.25/1.46         (((k1_mcart_1 @ X42) = (X41))
% 1.25/1.46          | ~ (r2_hidden @ X42 @ (k2_zfmisc_1 @ (k1_tarski @ X41) @ X43)))),
% 1.25/1.46      inference('cnf', [status(esa)], [t12_mcart_1])).
% 1.25/1.46  thf('102', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 1.25/1.46      inference('sup-', [status(thm)], ['100', '101'])).
% 1.25/1.46  thf('103', plain,
% 1.25/1.46      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 1.25/1.46         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 1.25/1.46      inference('split', [status(esa)], ['92'])).
% 1.25/1.46  thf('104', plain,
% 1.25/1.46      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 1.25/1.46       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_2))),
% 1.25/1.46      inference('split', [status(esa)], ['92'])).
% 1.25/1.46  thf('105', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 1.25/1.46      inference('sat_resolution*', [status(thm)], ['94', '104'])).
% 1.25/1.46  thf('106', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 1.25/1.46      inference('simpl_trail', [status(thm)], ['103', '105'])).
% 1.25/1.46  thf('107', plain, ($false),
% 1.25/1.46      inference('simplify_reflect-', [status(thm)], ['102', '106'])).
% 1.25/1.46  
% 1.25/1.46  % SZS output end Refutation
% 1.25/1.46  
% 1.31/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
