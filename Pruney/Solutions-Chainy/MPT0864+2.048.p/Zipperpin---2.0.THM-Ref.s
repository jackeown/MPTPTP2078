%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2t2dtA7hua

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:06 EST 2020

% Result     : Theorem 2.84s
% Output     : Refutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  182 (1312 expanded)
%              Number of leaves         :   31 ( 403 expanded)
%              Depth                    :   23
%              Number of atoms          : 2137 (13133 expanded)
%              Number of equality atoms :  223 (2054 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('0',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('4',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X49 @ X50 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('5',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('8',plain,(
    ! [X49: $i,X51: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X49 @ X51 ) )
      = X51 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('15',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('16',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X43 ) @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_tarski @ ( k4_tarski @ X43 @ X44 ) @ ( k4_tarski @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ ( k2_mcart_1 @ sk_A ) @ X0 ) )
        = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ X0 ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k2_tarski @ sk_A @ ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('22',plain,(
    ! [X52: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X52 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X37 @ X34 @ X35 ) @ ( sk_E_1 @ X37 @ X34 @ X35 ) @ X37 @ X34 @ X35 )
      | ( X36
       != ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X34: $i,X35: $i,X37: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X37 @ X34 @ X35 ) @ ( sk_E_1 @ X37 @ X34 @ X35 ) @ X37 @ X34 @ X35 )
      | ~ ( r2_hidden @ X37 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27
        = ( k4_tarski @ X25 @ X26 ) )
      | ~ ( zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = ( k4_tarski @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X49 @ X50 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X25 @ X29 )
      | ~ ( zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','34'])).

thf('36',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('37',plain,
    ( ( ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('44',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','48'])).

thf('50',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('52',plain,
    ( ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) @ ( sk_E_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) @ ( sk_B @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('56',plain,
    ( ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) @ ( sk_E_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('58',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) @ ( sk_E_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = ( k4_tarski @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('61',plain,(
    ! [X49: $i,X51: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X49 @ X51 ) )
      = X51 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
        = ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ) )
        = ( sk_F_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('65',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('66',plain,
    ( ( ( ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) )
        = ( sk_F_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('68',plain,
    ( ( ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( sk_F_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('71',plain,
    ( ( ( ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ) )
        = ( sk_E_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('73',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('74',plain,
    ( ( ( ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) )
        = ( sk_E_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('76',plain,
    ( ( ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( sk_E_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( zip_tseitin_0 @ ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','68','76'])).

thf('78',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27
        = ( k4_tarski @ X25 @ X26 ) )
      | ~ ( zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('79',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( r2_hidden @ X54 @ X52 )
      | ( ( sk_B @ X52 )
       != ( k4_tarski @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != ( sk_B @ ( k1_tarski @ sk_A ) ) )
        | ~ ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != ( sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','81'])).

thf('83',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('85',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['11','87'])).

thf('89',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('93',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X43 ) @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_tarski @ ( k4_tarski @ X43 @ X44 ) @ ( k4_tarski @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
        = ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('100',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ X28 )
      | ~ ( zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_zfmisc_1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('106',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X43 @ X44 ) @ ( k1_tarski @ X46 ) )
      = ( k2_tarski @ ( k4_tarski @ X43 @ X46 ) @ ( k4_tarski @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('109',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['104','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) @ ( sk_E_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) @ ( sk_B @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) @ ( sk_E_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) @ ( sk_E_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
        = ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) )
        = ( sk_F_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
        = ( sk_F_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      = ( sk_F_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) )
        = ( sk_E_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
        = ( sk_E_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      = ( sk_E_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['123','131','139'])).

thf('141',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27
        = ( k4_tarski @ X25 @ X26 ) )
      | ~ ( zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) @ ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( r2_hidden @ X53 @ X52 )
      | ( ( sk_B @ X52 )
       != ( k4_tarski @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_B @ X2 )
       != ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ X2 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
       != ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['114','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
     != ( sk_B @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

thf('148',plain,(
    ( sk_B @ ( k1_tarski @ sk_A ) )
 != ( sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','147'])).

thf('149',plain,(
    $false ),
    inference(simplify,[status(thm)],['148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2t2dtA7hua
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.84/3.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.84/3.07  % Solved by: fo/fo7.sh
% 2.84/3.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.84/3.07  % done 4042 iterations in 2.604s
% 2.84/3.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.84/3.07  % SZS output start Refutation
% 2.84/3.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.84/3.07  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 2.84/3.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.84/3.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 2.84/3.07  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 2.84/3.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.84/3.07  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.84/3.07  thf(sk_B_type, type, sk_B: $i > $i).
% 2.84/3.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.84/3.07  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 2.84/3.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.84/3.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.84/3.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.84/3.07  thf(sk_A_type, type, sk_A: $i).
% 2.84/3.07  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 2.84/3.07  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.84/3.07  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.84/3.07  thf(sk_C_type, type, sk_C: $i).
% 2.84/3.07  thf(t20_mcart_1, conjecture,
% 2.84/3.07    (![A:$i]:
% 2.84/3.07     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 2.84/3.07       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 2.84/3.07  thf(zf_stmt_0, negated_conjecture,
% 2.84/3.07    (~( ![A:$i]:
% 2.84/3.07        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 2.84/3.07          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 2.84/3.07    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 2.84/3.07  thf('0', plain,
% 2.84/3.07      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.84/3.07  thf('1', plain,
% 2.84/3.07      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('split', [status(esa)], ['0'])).
% 2.84/3.07  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.84/3.07  thf('3', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.84/3.07  thf(t7_mcart_1, axiom,
% 2.84/3.07    (![A:$i,B:$i]:
% 2.84/3.07     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 2.84/3.07       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 2.84/3.07  thf('4', plain,
% 2.84/3.07      (![X49 : $i, X50 : $i]: ((k1_mcart_1 @ (k4_tarski @ X49 @ X50)) = (X49))),
% 2.84/3.07      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.84/3.07  thf('5', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 2.84/3.07      inference('sup+', [status(thm)], ['3', '4'])).
% 2.84/3.07  thf('6', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C))),
% 2.84/3.07      inference('demod', [status(thm)], ['2', '5'])).
% 2.84/3.07  thf('7', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C))),
% 2.84/3.07      inference('demod', [status(thm)], ['2', '5'])).
% 2.84/3.07  thf('8', plain,
% 2.84/3.07      (![X49 : $i, X51 : $i]: ((k2_mcart_1 @ (k4_tarski @ X49 @ X51)) = (X51))),
% 2.84/3.07      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.84/3.07  thf('9', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 2.84/3.07      inference('sup+', [status(thm)], ['7', '8'])).
% 2.84/3.07  thf('10', plain,
% 2.84/3.07      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 2.84/3.07      inference('demod', [status(thm)], ['6', '9'])).
% 2.84/3.07  thf('11', plain,
% 2.84/3.07      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['1', '10'])).
% 2.84/3.07  thf(t69_enumset1, axiom,
% 2.84/3.07    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.84/3.07  thf('12', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 2.84/3.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.84/3.07  thf('13', plain,
% 2.84/3.07      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('split', [status(esa)], ['0'])).
% 2.84/3.07  thf('14', plain,
% 2.84/3.07      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 2.84/3.07      inference('demod', [status(thm)], ['6', '9'])).
% 2.84/3.07  thf('15', plain,
% 2.84/3.07      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['13', '14'])).
% 2.84/3.07  thf(t36_zfmisc_1, axiom,
% 2.84/3.07    (![A:$i,B:$i,C:$i]:
% 2.84/3.07     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 2.84/3.07         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 2.84/3.07       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 2.84/3.07         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 2.84/3.07  thf('16', plain,
% 2.84/3.07      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X43) @ (k2_tarski @ X44 @ X45))
% 2.84/3.07           = (k2_tarski @ (k4_tarski @ X43 @ X44) @ (k4_tarski @ X43 @ X45)))),
% 2.84/3.07      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 2.84/3.07  thf('17', plain,
% 2.84/3.07      ((![X0 : $i]:
% 2.84/3.07          ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07            (k2_tarski @ (k2_mcart_1 @ sk_A) @ X0))
% 2.84/3.07            = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ X0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['15', '16'])).
% 2.84/3.07  thf('18', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k2_tarski @ sk_A @ (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A)))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['12', '17'])).
% 2.84/3.07  thf('19', plain,
% 2.84/3.07      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['13', '14'])).
% 2.84/3.07  thf('20', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 2.84/3.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.84/3.07  thf('21', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf(t9_mcart_1, axiom,
% 2.84/3.07    (![A:$i]:
% 2.84/3.07     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.84/3.07          ( ![B:$i]:
% 2.84/3.07            ( ~( ( r2_hidden @ B @ A ) & 
% 2.84/3.07                 ( ![C:$i,D:$i]:
% 2.84/3.07                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 2.84/3.07                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 2.84/3.07  thf('22', plain,
% 2.84/3.07      (![X52 : $i]:
% 2.84/3.07         (((X52) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X52) @ X52))),
% 2.84/3.07      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.84/3.07  thf(d2_zfmisc_1, axiom,
% 2.84/3.07    (![A:$i,B:$i,C:$i]:
% 2.84/3.07     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.84/3.07       ( ![D:$i]:
% 2.84/3.07         ( ( r2_hidden @ D @ C ) <=>
% 2.84/3.07           ( ?[E:$i,F:$i]:
% 2.84/3.07             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 2.84/3.07               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 2.84/3.07  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 2.84/3.07  thf(zf_stmt_2, axiom,
% 2.84/3.07    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 2.84/3.07     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 2.84/3.07       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 2.84/3.07         ( r2_hidden @ E @ A ) ) ))).
% 2.84/3.07  thf(zf_stmt_3, axiom,
% 2.84/3.07    (![A:$i,B:$i,C:$i]:
% 2.84/3.07     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.84/3.07       ( ![D:$i]:
% 2.84/3.07         ( ( r2_hidden @ D @ C ) <=>
% 2.84/3.07           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 2.84/3.07  thf('23', plain,
% 2.84/3.07      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.84/3.07         (~ (r2_hidden @ X37 @ X36)
% 2.84/3.07          | (zip_tseitin_0 @ (sk_F_1 @ X37 @ X34 @ X35) @ 
% 2.84/3.07             (sk_E_1 @ X37 @ X34 @ X35) @ X37 @ X34 @ X35)
% 2.84/3.07          | ((X36) != (k2_zfmisc_1 @ X35 @ X34)))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.84/3.07  thf('24', plain,
% 2.84/3.07      (![X34 : $i, X35 : $i, X37 : $i]:
% 2.84/3.07         ((zip_tseitin_0 @ (sk_F_1 @ X37 @ X34 @ X35) @ 
% 2.84/3.07           (sk_E_1 @ X37 @ X34 @ X35) @ X37 @ X34 @ X35)
% 2.84/3.07          | ~ (r2_hidden @ X37 @ (k2_zfmisc_1 @ X35 @ X34)))),
% 2.84/3.07      inference('simplify', [status(thm)], ['23'])).
% 2.84/3.07  thf('25', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | (zip_tseitin_0 @ 
% 2.84/3.07             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 2.84/3.07      inference('sup-', [status(thm)], ['22', '24'])).
% 2.84/3.07  thf('26', plain,
% 2.84/3.07      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.84/3.07         (((X27) = (k4_tarski @ X25 @ X26))
% 2.84/3.07          | ~ (zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.84/3.07  thf('27', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 2.84/3.07          | ((sk_B @ (k2_zfmisc_1 @ X0 @ X1))
% 2.84/3.07              = (k4_tarski @ 
% 2.84/3.07                 (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ 
% 2.84/3.07                 (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0))))),
% 2.84/3.07      inference('sup-', [status(thm)], ['25', '26'])).
% 2.84/3.07  thf('28', plain,
% 2.84/3.07      (![X49 : $i, X50 : $i]: ((k1_mcart_1 @ (k4_tarski @ X49 @ X50)) = (X49))),
% 2.84/3.07      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.84/3.07  thf('29', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.84/3.07            = (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['27', '28'])).
% 2.84/3.07  thf('30', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | (zip_tseitin_0 @ 
% 2.84/3.07             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 2.84/3.07      inference('sup-', [status(thm)], ['22', '24'])).
% 2.84/3.07  thf('31', plain,
% 2.84/3.07      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.84/3.07         ((r2_hidden @ X25 @ X29)
% 2.84/3.07          | ~ (zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.84/3.07  thf('32', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 2.84/3.07          | (r2_hidden @ 
% 2.84/3.07             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['30', '31'])).
% 2.84/3.07  thf('33', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1)
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['29', '32'])).
% 2.84/3.07  thf('34', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 2.84/3.07      inference('simplify', [status(thm)], ['33'])).
% 2.84/3.07  thf('35', plain,
% 2.84/3.07      ((((r2_hidden @ (k1_mcart_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.84/3.07          (k1_tarski @ sk_A))
% 2.84/3.07         | ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A))) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['21', '34'])).
% 2.84/3.07  thf('36', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('37', plain,
% 2.84/3.07      ((((r2_hidden @ (k1_mcart_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.84/3.07          (k1_tarski @ sk_A))
% 2.84/3.07         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['35', '36'])).
% 2.84/3.07  thf(t70_enumset1, axiom,
% 2.84/3.07    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.84/3.07  thf('38', plain,
% 2.84/3.07      (![X5 : $i, X6 : $i]:
% 2.84/3.07         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 2.84/3.07      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.84/3.07  thf('39', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 2.84/3.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.84/3.07  thf('40', plain,
% 2.84/3.07      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.84/3.07      inference('sup+', [status(thm)], ['38', '39'])).
% 2.84/3.07  thf(t71_enumset1, axiom,
% 2.84/3.07    (![A:$i,B:$i,C:$i]:
% 2.84/3.07     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.84/3.07  thf('41', plain,
% 2.84/3.07      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.84/3.07         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 2.84/3.07      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.84/3.07  thf(t46_enumset1, axiom,
% 2.84/3.07    (![A:$i,B:$i,C:$i,D:$i]:
% 2.84/3.07     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 2.84/3.07       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 2.84/3.07  thf('42', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.84/3.07         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 2.84/3.07           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ (k1_tarski @ X3)))),
% 2.84/3.07      inference('cnf', [status(esa)], [t46_enumset1])).
% 2.84/3.07  thf('43', plain,
% 2.84/3.07      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.84/3.07      inference('sup+', [status(thm)], ['38', '39'])).
% 2.84/3.07  thf(t49_zfmisc_1, axiom,
% 2.84/3.07    (![A:$i,B:$i]:
% 2.84/3.07     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 2.84/3.07  thf('44', plain,
% 2.84/3.07      (![X47 : $i, X48 : $i]:
% 2.84/3.07         ((k2_xboole_0 @ (k1_tarski @ X47) @ X48) != (k1_xboole_0))),
% 2.84/3.07      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 2.84/3.07  thf('45', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ X1) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['43', '44'])).
% 2.84/3.07  thf('46', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['42', '45'])).
% 2.84/3.07  thf('47', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]: ((k1_enumset1 @ X1 @ X1 @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['41', '46'])).
% 2.84/3.07  thf('48', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('49', plain,
% 2.84/3.07      (((r2_hidden @ (k1_mcart_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.84/3.07         (k1_tarski @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['37', '48'])).
% 2.84/3.07  thf('50', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('51', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | (zip_tseitin_0 @ 
% 2.84/3.07             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 2.84/3.07      inference('sup-', [status(thm)], ['22', '24'])).
% 2.84/3.07  thf('52', plain,
% 2.84/3.07      ((((zip_tseitin_0 @ 
% 2.84/3.07          (sk_F_1 @ 
% 2.84/3.07           (sk_B @ 
% 2.84/3.07            (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A)))) @ 
% 2.84/3.07           (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07          (sk_E_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07           (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07          (sk_B @ 
% 2.84/3.07           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07            (k1_tarski @ (k2_mcart_1 @ sk_A)))) @ 
% 2.84/3.07          (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A))
% 2.84/3.07         | ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A))) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['50', '51'])).
% 2.84/3.07  thf('53', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('54', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('55', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('56', plain,
% 2.84/3.07      ((((zip_tseitin_0 @ 
% 2.84/3.07          (sk_F_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07           (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07          (sk_E_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07           (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07          (sk_B @ (k1_tarski @ sk_A)) @ (k1_tarski @ (k2_mcart_1 @ sk_A)) @ 
% 2.84/3.07          (k1_tarski @ sk_A))
% 2.84/3.07         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 2.84/3.07  thf('57', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('58', plain,
% 2.84/3.07      (((zip_tseitin_0 @ 
% 2.84/3.07         (sk_F_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07          (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07         (sk_E_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07          (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07         (sk_B @ (k1_tarski @ sk_A)) @ (k1_tarski @ (k2_mcart_1 @ sk_A)) @ 
% 2.84/3.07         (k1_tarski @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 2.84/3.07  thf('59', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('60', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 2.84/3.07          | ((sk_B @ (k2_zfmisc_1 @ X0 @ X1))
% 2.84/3.07              = (k4_tarski @ 
% 2.84/3.07                 (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ 
% 2.84/3.07                 (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0))))),
% 2.84/3.07      inference('sup-', [status(thm)], ['25', '26'])).
% 2.84/3.07  thf('61', plain,
% 2.84/3.07      (![X49 : $i, X51 : $i]: ((k2_mcart_1 @ (k4_tarski @ X49 @ X51)) = (X51))),
% 2.84/3.07      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.84/3.07  thf('62', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.84/3.07            = (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['60', '61'])).
% 2.84/3.07  thf('63', plain,
% 2.84/3.07      (((((k2_mcart_1 @ 
% 2.84/3.07           (sk_B @ 
% 2.84/3.07            (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A)))))
% 2.84/3.07           = (sk_F_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07              (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)))
% 2.84/3.07         | ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A))) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['59', '62'])).
% 2.84/3.07  thf('64', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('65', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('66', plain,
% 2.84/3.07      (((((k2_mcart_1 @ (sk_B @ (k1_tarski @ sk_A)))
% 2.84/3.07           = (sk_F_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07              (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)))
% 2.84/3.07         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.84/3.07  thf('67', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('68', plain,
% 2.84/3.07      ((((k2_mcart_1 @ (sk_B @ (k1_tarski @ sk_A)))
% 2.84/3.07          = (sk_F_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 2.84/3.07  thf('69', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('70', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.84/3.07            = (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['27', '28'])).
% 2.84/3.07  thf('71', plain,
% 2.84/3.07      (((((k1_mcart_1 @ 
% 2.84/3.07           (sk_B @ 
% 2.84/3.07            (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A)))))
% 2.84/3.07           = (sk_E_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07              (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)))
% 2.84/3.07         | ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A))) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup+', [status(thm)], ['69', '70'])).
% 2.84/3.07  thf('72', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('73', plain,
% 2.84/3.07      ((((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 2.84/3.07          = (k1_tarski @ sk_A)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.84/3.07  thf('74', plain,
% 2.84/3.07      (((((k1_mcart_1 @ (sk_B @ (k1_tarski @ sk_A)))
% 2.84/3.07           = (sk_E_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07              (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A)))
% 2.84/3.07         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['71', '72', '73'])).
% 2.84/3.07  thf('75', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('76', plain,
% 2.84/3.07      ((((k1_mcart_1 @ (sk_B @ (k1_tarski @ sk_A)))
% 2.84/3.07          = (sk_E_1 @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.84/3.07             (k1_tarski @ (k2_mcart_1 @ sk_A)) @ (k1_tarski @ sk_A))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 2.84/3.07  thf('77', plain,
% 2.84/3.07      (((zip_tseitin_0 @ (k2_mcart_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.84/3.07         (k1_mcart_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.84/3.07         (sk_B @ (k1_tarski @ sk_A)) @ (k1_tarski @ (k2_mcart_1 @ sk_A)) @ 
% 2.84/3.07         (k1_tarski @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('demod', [status(thm)], ['58', '68', '76'])).
% 2.84/3.07  thf('78', plain,
% 2.84/3.07      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.84/3.07         (((X27) = (k4_tarski @ X25 @ X26))
% 2.84/3.07          | ~ (zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.84/3.07  thf('79', plain,
% 2.84/3.07      ((((sk_B @ (k1_tarski @ sk_A))
% 2.84/3.07          = (k4_tarski @ (k1_mcart_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.84/3.07             (k2_mcart_1 @ (sk_B @ (k1_tarski @ sk_A))))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup-', [status(thm)], ['77', '78'])).
% 2.84/3.07  thf('80', plain,
% 2.84/3.07      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.84/3.07         (((X52) = (k1_xboole_0))
% 2.84/3.07          | ~ (r2_hidden @ X54 @ X52)
% 2.84/3.07          | ((sk_B @ X52) != (k4_tarski @ X54 @ X53)))),
% 2.84/3.07      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.84/3.07  thf('81', plain,
% 2.84/3.07      ((![X0 : $i]:
% 2.84/3.07          (((sk_B @ X0) != (sk_B @ (k1_tarski @ sk_A)))
% 2.84/3.07           | ~ (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k1_tarski @ sk_A))) @ X0)
% 2.84/3.07           | ((X0) = (k1_xboole_0))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup-', [status(thm)], ['79', '80'])).
% 2.84/3.07  thf('82', plain,
% 2.84/3.07      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.84/3.07         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_B @ (k1_tarski @ sk_A)))))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('sup-', [status(thm)], ['49', '81'])).
% 2.84/3.07  thf('83', plain,
% 2.84/3.07      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 2.84/3.07         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 2.84/3.07      inference('simplify', [status(thm)], ['82'])).
% 2.84/3.07  thf('84', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('85', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 2.84/3.07  thf('86', plain,
% 2.84/3.07      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 2.84/3.07      inference('split', [status(esa)], ['0'])).
% 2.84/3.07  thf('87', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 2.84/3.07      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 2.84/3.07  thf('88', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A))),
% 2.84/3.07      inference('simpl_trail', [status(thm)], ['11', '87'])).
% 2.84/3.07  thf('89', plain,
% 2.84/3.07      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.84/3.07         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 2.84/3.07      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.84/3.07  thf('90', plain,
% 2.84/3.07      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.84/3.07      inference('sup+', [status(thm)], ['38', '39'])).
% 2.84/3.07  thf('91', plain,
% 2.84/3.07      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.84/3.07      inference('sup+', [status(thm)], ['89', '90'])).
% 2.84/3.07  thf('92', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 2.84/3.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.84/3.07  thf('93', plain,
% 2.84/3.07      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X43) @ (k2_tarski @ X44 @ X45))
% 2.84/3.07           = (k2_tarski @ (k4_tarski @ X43 @ X44) @ (k4_tarski @ X43 @ X45)))),
% 2.84/3.07      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 2.84/3.07  thf('94', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['92', '93'])).
% 2.84/3.07  thf('95', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 2.84/3.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.84/3.07  thf('96', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('97', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k2_enumset1 @ X0 @ X0 @ X0 @ X0) @ (k1_tarski @ X1))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X0 @ X1)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['91', '96'])).
% 2.84/3.07  thf('98', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.84/3.07            = (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['60', '61'])).
% 2.84/3.07  thf('99', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | (zip_tseitin_0 @ 
% 2.84/3.07             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 2.84/3.07      inference('sup-', [status(thm)], ['22', '24'])).
% 2.84/3.07  thf('100', plain,
% 2.84/3.07      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.84/3.07         ((r2_hidden @ X26 @ X28)
% 2.84/3.07          | ~ (zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.84/3.07  thf('101', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 2.84/3.07          | (r2_hidden @ 
% 2.84/3.07             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 2.84/3.07      inference('sup-', [status(thm)], ['99', '100'])).
% 2.84/3.07  thf('102', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0)
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['98', '101'])).
% 2.84/3.07  thf('103', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 2.84/3.07      inference('simplify', [status(thm)], ['102'])).
% 2.84/3.07  thf('104', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((r2_hidden @ 
% 2.84/3.07           (k2_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 2.84/3.07           (k1_tarski @ X0))
% 2.84/3.07          | ((k2_zfmisc_1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X1) @ 
% 2.84/3.07              (k1_tarski @ X0)) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['97', '103'])).
% 2.84/3.07  thf('105', plain,
% 2.84/3.07      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.84/3.07         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 2.84/3.07      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.84/3.07  thf('106', plain,
% 2.84/3.07      (![X5 : $i, X6 : $i]:
% 2.84/3.07         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 2.84/3.07      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.84/3.07  thf('107', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.84/3.07      inference('sup+', [status(thm)], ['105', '106'])).
% 2.84/3.07  thf('108', plain,
% 2.84/3.07      (![X43 : $i, X44 : $i, X46 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k2_tarski @ X43 @ X44) @ (k1_tarski @ X46))
% 2.84/3.07           = (k2_tarski @ (k4_tarski @ X43 @ X46) @ (k4_tarski @ X44 @ X46)))),
% 2.84/3.07      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 2.84/3.07  thf('109', plain,
% 2.84/3.07      (![X5 : $i, X6 : $i]:
% 2.84/3.07         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 2.84/3.07      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.84/3.07  thf('110', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]: ((k1_enumset1 @ X1 @ X1 @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['41', '46'])).
% 2.84/3.07  thf('111', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['109', '110'])).
% 2.84/3.07  thf('112', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['108', '111'])).
% 2.84/3.07  thf('113', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2))
% 2.84/3.07           != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['107', '112'])).
% 2.84/3.07  thf('114', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (r2_hidden @ 
% 2.84/3.07          (k2_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 2.84/3.07          (k1_tarski @ X0))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['104', '113'])).
% 2.84/3.07  thf('115', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('116', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.84/3.07          | (zip_tseitin_0 @ 
% 2.84/3.07             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.84/3.07             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 2.84/3.07      inference('sup-', [status(thm)], ['22', '24'])).
% 2.84/3.07  thf('117', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((zip_tseitin_0 @ 
% 2.84/3.07           (sk_F_1 @ 
% 2.84/3.07            (sk_B @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))) @ 
% 2.84/3.07            (k1_tarski @ X0) @ (k1_tarski @ X1)) @ 
% 2.84/3.07           (sk_E_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07            (k1_tarski @ X0) @ (k1_tarski @ X1)) @ 
% 2.84/3.07           (sk_B @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))) @ 
% 2.84/3.07           (k1_tarski @ X0) @ (k1_tarski @ X1))
% 2.84/3.07          | ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07              = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['115', '116'])).
% 2.84/3.07  thf('118', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('119', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('120', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('121', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((zip_tseitin_0 @ 
% 2.84/3.07           (sk_F_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07            (k1_tarski @ X0) @ (k1_tarski @ X1)) @ 
% 2.84/3.07           (sk_E_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07            (k1_tarski @ X0) @ (k1_tarski @ X1)) @ 
% 2.84/3.07           (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ (k1_tarski @ X0) @ 
% 2.84/3.07           (k1_tarski @ X1))
% 2.84/3.07          | ((k1_tarski @ (k4_tarski @ X1 @ X0)) = (k1_xboole_0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 2.84/3.07  thf('122', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('123', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (zip_tseitin_0 @ 
% 2.84/3.07          (sk_F_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07           (k1_tarski @ X0) @ (k1_tarski @ X1)) @ 
% 2.84/3.07          (sk_E_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07           (k1_tarski @ X0) @ (k1_tarski @ X1)) @ 
% 2.84/3.07          (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ (k1_tarski @ X0) @ 
% 2.84/3.07          (k1_tarski @ X1))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 2.84/3.07  thf('124', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('125', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.84/3.07            = (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['60', '61'])).
% 2.84/3.07  thf('126', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_mcart_1 @ 
% 2.84/3.07            (sk_B @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))
% 2.84/3.07            = (sk_F_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07               (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 2.84/3.07          | ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07              = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['124', '125'])).
% 2.84/3.07  thf('127', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('128', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('129', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k2_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 2.84/3.07            = (sk_F_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07               (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 2.84/3.07          | ((k1_tarski @ (k4_tarski @ X1 @ X0)) = (k1_xboole_0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['126', '127', '128'])).
% 2.84/3.07  thf('130', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('131', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 2.84/3.07           = (sk_F_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07              (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['129', '130'])).
% 2.84/3.07  thf('132', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('133', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.84/3.07            = (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))
% 2.84/3.07          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['27', '28'])).
% 2.84/3.07  thf('134', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k1_mcart_1 @ 
% 2.84/3.07            (sk_B @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))
% 2.84/3.07            = (sk_E_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07               (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 2.84/3.07          | ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07              = (k1_xboole_0)))),
% 2.84/3.07      inference('sup+', [status(thm)], ['132', '133'])).
% 2.84/3.07  thf('135', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('136', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 2.84/3.07           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['94', '95'])).
% 2.84/3.07  thf('137', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k1_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 2.84/3.07            = (sk_E_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07               (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 2.84/3.07          | ((k1_tarski @ (k4_tarski @ X1 @ X0)) = (k1_xboole_0)))),
% 2.84/3.07      inference('demod', [status(thm)], ['134', '135', '136'])).
% 2.84/3.07  thf('138', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('139', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((k1_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 2.84/3.07           = (sk_E_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 2.84/3.07              (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 2.84/3.07  thf('140', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (zip_tseitin_0 @ 
% 2.84/3.07          (k2_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 2.84/3.07          (k1_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 2.84/3.07          (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ (k1_tarski @ X0) @ 
% 2.84/3.07          (k1_tarski @ X1))),
% 2.84/3.07      inference('demod', [status(thm)], ['123', '131', '139'])).
% 2.84/3.07  thf('141', plain,
% 2.84/3.07      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.84/3.07         (((X27) = (k4_tarski @ X25 @ X26))
% 2.84/3.07          | ~ (zip_tseitin_0 @ X26 @ X25 @ X27 @ X28 @ X29))),
% 2.84/3.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.84/3.07  thf('142', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((sk_B @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 2.84/3.07           = (k4_tarski @ 
% 2.84/3.07              (k1_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X0 @ X1)))) @ 
% 2.84/3.07              (k2_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X0 @ X1))))))),
% 2.84/3.07      inference('sup-', [status(thm)], ['140', '141'])).
% 2.84/3.07  thf('143', plain,
% 2.84/3.07      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.84/3.07         (((X52) = (k1_xboole_0))
% 2.84/3.07          | ~ (r2_hidden @ X53 @ X52)
% 2.84/3.07          | ((sk_B @ X52) != (k4_tarski @ X54 @ X53)))),
% 2.84/3.07      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.84/3.07  thf('144', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.07         (((sk_B @ X2) != (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 2.84/3.07          | ~ (r2_hidden @ 
% 2.84/3.07               (k2_mcart_1 @ (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ X2)
% 2.84/3.07          | ((X2) = (k1_xboole_0)))),
% 2.84/3.07      inference('sup-', [status(thm)], ['142', '143'])).
% 2.84/3.07  thf('145', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         (((k1_tarski @ X0) = (k1_xboole_0))
% 2.84/3.07          | ((sk_B @ (k1_tarski @ X0))
% 2.84/3.07              != (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0)))))),
% 2.84/3.07      inference('sup-', [status(thm)], ['114', '144'])).
% 2.84/3.07  thf('146', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.84/3.07      inference('sup-', [status(thm)], ['40', '47'])).
% 2.84/3.07  thf('147', plain,
% 2.84/3.07      (![X0 : $i, X1 : $i]:
% 2.84/3.07         ((sk_B @ (k1_tarski @ X0))
% 2.84/3.07           != (sk_B @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 2.84/3.07      inference('simplify_reflect-', [status(thm)], ['145', '146'])).
% 2.84/3.07  thf('148', plain,
% 2.84/3.07      (((sk_B @ (k1_tarski @ sk_A)) != (sk_B @ (k1_tarski @ sk_A)))),
% 2.84/3.07      inference('sup-', [status(thm)], ['88', '147'])).
% 2.84/3.07  thf('149', plain, ($false), inference('simplify', [status(thm)], ['148'])).
% 2.84/3.07  
% 2.84/3.07  % SZS output end Refutation
% 2.84/3.07  
% 2.84/3.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
