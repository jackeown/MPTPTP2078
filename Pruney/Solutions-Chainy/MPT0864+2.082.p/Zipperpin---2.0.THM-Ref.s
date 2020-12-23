%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gWWXlM0ovN

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 (1533 expanded)
%              Number of leaves         :   29 ( 442 expanded)
%              Depth                    :   23
%              Number of atoms          :  836 (15128 expanded)
%              Number of equality atoms :  149 (2637 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf('0',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
        = ( k1_tarski @ X12 ) )
      | ( X12 = X13 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X16 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X15 @ ( k1_tarski @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X15 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('9',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ( ( sk_B @ X23 )
       != ( k4_tarski @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('22',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X20: $i,X22: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X20 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('26',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ( ( sk_B @ X23 )
       != ( k4_tarski @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X9 ) @ ( k2_tarski @ X9 @ X10 ) )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k1_setfam_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('44',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('45',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 != X11 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X11 ) )
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X11 ) )
     != ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('59',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_A ) )
     != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['20','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('62',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['60','61'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('63',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('65',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X11 ) )
     != ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ( k4_xboole_0 @ ( k2_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('72',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('73',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['60','61'])).

thf('76',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['60','61'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('78',plain,
    ( ( k1_setfam_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('80',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['60','61'])).

thf('81',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('85',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['60','61'])).

thf('87',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','74','75','85','86'])).

thf('88',plain,(
    $false ),
    inference(simplify,[status(thm)],['87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gWWXlM0ovN
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 11:54:36 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 147 iterations in 0.059s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.54  thf(t9_mcart_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.54                 ( ![C:$i,D:$i]:
% 0.22/0.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.54                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (![X23 : $i]:
% 0.22/0.54         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.22/0.54      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.54  thf(t20_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.54         ( k1_tarski @ A ) ) <=>
% 0.22/0.54       ( ( A ) != ( B ) ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X12 : $i, X13 : $i]:
% 0.22/0.54         (((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13))
% 0.22/0.54            = (k1_tarski @ X12))
% 0.22/0.54          | ((X12) = (X13)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.54  thf(t64_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.54       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.54         (((X14) != (X16))
% 0.22/0.54          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X15 @ (k1_tarski @ X16))))),
% 0.22/0.54      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i]:
% 0.22/0.54         ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X15 @ (k1_tarski @ X16)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.54          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X23 : $i]:
% 0.22/0.54         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.22/0.54      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.22/0.54          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.54          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.54  thf(t20_mcart_1, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.54       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.54          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.22/0.54  thf('9', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t7_mcart_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.54       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i]: ((k1_mcart_1 @ (k4_tarski @ X20 @ X21)) = (X20))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.54  thf('11', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.22/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['11', '13'])).
% 0.22/0.54  thf('15', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.22/0.54         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.54         (((X23) = (k1_xboole_0))
% 0.22/0.54          | ~ (r2_hidden @ X25 @ X23)
% 0.22/0.54          | ((sk_B @ X23) != (k4_tarski @ X25 @ X24)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (((sk_B @ X0) != (sk_A))
% 0.22/0.54           | ~ (r2_hidden @ sk_A @ X0)
% 0.22/0.54           | ((X0) = (k1_xboole_0))))
% 0.22/0.54         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.54         | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.54         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.22/0.54         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (((((sk_B @ (k1_tarski @ sk_A)) != (sk_A))
% 0.22/0.54         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.22/0.54         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.54          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.54  thf('22', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X20 : $i, X22 : $i]: ((k2_mcart_1 @ (k4_tarski @ X20 @ X22)) = (X22))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.54  thf('24', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.22/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['12'])).
% 0.22/0.54  thf('26', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf('27', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.54         (((X23) = (k1_xboole_0))
% 0.22/0.54          | ~ (r2_hidden @ X24 @ X23)
% 0.22/0.54          | ((sk_B @ X23) != (k4_tarski @ X25 @ X24)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (((sk_B @ X0) != (sk_A))
% 0.22/0.54           | ~ (r2_hidden @ sk_A @ X0)
% 0.22/0.54           | ((X0) = (k1_xboole_0))))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.54         | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.54         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['21', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (((((sk_B @ (k1_tarski @ sk_A)) != (sk_A))
% 0.22/0.54         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.54          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf(t69_enumset1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.54  thf('35', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.54  thf(t19_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.22/0.54       ( k1_tarski @ A ) ))).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ (k1_tarski @ X9) @ (k2_tarski @ X9 @ X10))
% 0.22/0.54           = (k1_tarski @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.22/0.54           = (k1_tarski @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.54  thf(t12_setfam_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['37', '40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((((k1_setfam_1 @ (k1_tarski @ k1_xboole_0)) = (k1_tarski @ sk_A)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['34', '41'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.54  thf(t100_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.54          = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['45', '46'])).
% 0.22/0.54  thf(t92_xboole_1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('48', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X11 : $i, X12 : $i]:
% 0.22/0.54         (((X12) != (X11))
% 0.22/0.54          | ((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X11))
% 0.22/0.54              != (k1_tarski @ X12)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (![X11 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X11))
% 0.22/0.54           != (k1_tarski @ X11))),
% 0.22/0.54      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['50', '52'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.22/0.54  thf('57', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['49', '56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['12'])).
% 0.22/0.54  thf('59', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      ((((sk_B @ (k1_tarski @ sk_A)) != (sk_A))
% 0.22/0.54        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['20', '59'])).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.22/0.54          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.54  thf('62', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf(t71_enumset1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.54         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.22/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.54  thf(t70_enumset1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.54  thf('64', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]:
% 0.22/0.54         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.54  thf('65', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.54  thf('66', plain,
% 0.22/0.54      (![X11 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X11))
% 0.22/0.54           != (k1_tarski @ X11))),
% 0.22/0.54      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.54  thf('67', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.22/0.54           != (k1_tarski @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.54  thf('68', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k1_tarski @ X0))
% 0.22/0.54           != (k1_tarski @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['64', '67'])).
% 0.22/0.54  thf('69', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ (k2_enumset1 @ X0 @ X0 @ X0 @ X0) @ (k1_tarski @ X0))
% 0.22/0.54           != (k1_tarski @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['63', '68'])).
% 0.22/0.54  thf('70', plain,
% 0.22/0.54      (((k4_xboole_0 @ (k2_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A) @ k1_xboole_0)
% 0.22/0.54         != (k1_tarski @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['62', '69'])).
% 0.22/0.54  thf('71', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.54         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.22/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.54  thf('72', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]:
% 0.22/0.54         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.54  thf('73', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.54  thf('74', plain,
% 0.22/0.54      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['72', '73'])).
% 0.22/0.54  thf('75', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf('76', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf('77', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['37', '40'])).
% 0.22/0.54  thf('78', plain,
% 0.22/0.54      (((k1_setfam_1 @ (k1_tarski @ k1_xboole_0)) = (k1_tarski @ sk_A))),
% 0.22/0.54      inference('sup+', [status(thm)], ['76', '77'])).
% 0.22/0.54  thf('79', plain,
% 0.22/0.54      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.54  thf('80', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf('81', plain,
% 0.22/0.54      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.22/0.54  thf('82', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.54  thf('83', plain,
% 0.22/0.54      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.54         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['81', '82'])).
% 0.22/0.54  thf('84', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.54  thf('85', plain,
% 0.22/0.54      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['83', '84'])).
% 0.22/0.54  thf('86', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf('87', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['70', '71', '74', '75', '85', '86'])).
% 0.22/0.54  thf('88', plain, ($false), inference('simplify', [status(thm)], ['87'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
