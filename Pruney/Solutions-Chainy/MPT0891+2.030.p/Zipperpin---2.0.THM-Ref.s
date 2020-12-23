%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sGEl1MVbrk

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 (1327 expanded)
%              Number of leaves         :   30 ( 407 expanded)
%              Depth                    :   16
%              Number of atoms          : 1341 (28366 expanded)
%              Number of equality atoms :  181 (4470 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t51_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( D
                 != ( k5_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k6_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( D
                   != ( k5_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k6_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_mcart_1])).

thf('0',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X18
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X15 @ X16 @ X17 @ X18 ) @ ( k6_mcart_1 @ X15 @ X16 @ X17 @ X18 ) @ ( k7_mcart_1 @ X15 @ X16 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('4',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X22 @ X23 @ X25 @ X24 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k3_zfmisc_1 @ X22 @ X23 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('7',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X22 @ X23 @ X25 @ X24 )
        = ( k2_mcart_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k3_zfmisc_1 @ X22 @ X23 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('14',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','11','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ sk_D @ ( k2_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf(t41_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) )
      = ( k2_tarski @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k2_tarski @ X12 @ X14 ) @ ( k1_tarski @ X13 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ ( k3_mcart_1 @ X11 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_mcart_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t49_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k3_zfmisc_1 @ X21 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( r1_tarski @ ( k2_tarski @ sk_D @ sk_D ) @ ( k1_tarski @ sk_D ) )
      | ( ( k2_tarski @ sk_D @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k1_tarski @ X7 ) )
      | ( X6
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('33',plain,(
    ! [X7: $i] :
      ( r1_tarski @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','31','33','34'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X9 @ ( k1_tarski @ X8 ) )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_D @ X0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10'])).

thf('42',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('45',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ sk_D @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X7: $i] :
      ( r1_tarski @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X9 @ ( k1_tarski @ X8 ) )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_D @ X0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( ( k3_xboole_0 @ X4 @ ( k1_tarski @ X3 ) )
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
         != ( k1_tarski @ sk_D ) )
        | ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_D @ X0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['14','15','16','17'])).

thf('66',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('69',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('71',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k3_zfmisc_1 @ X20 @ X21 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k1_tarski @ sk_D ) )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X7: $i] :
      ( r1_tarski @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('75',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X9 @ ( k1_tarski @ X8 ) )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_D @ X0 )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( ( k3_xboole_0 @ X4 @ ( k1_tarski @ X3 ) )
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
         != ( k1_tarski @ sk_D ) )
        | ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_D @ X0 )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['80','87'])).

thf('89',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['64','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ X0 ) ),
    inference(simpl_trail,[status(thm)],['40','90'])).

thf('92',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','31','33','34'])).

thf('93',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( ( k3_xboole_0 @ X4 @ ( k1_tarski @ X3 ) )
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
         != ( k1_tarski @ sk_D ) )
        | ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('96',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['30','31','33','34'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_D @ X0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['64','88','89'])).

thf('100',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference(simpl_trail,[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['91','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sGEl1MVbrk
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 179 iterations in 0.135s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.58  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.58  thf(t51_mcart_1, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58          ( ~( ![D:$i]:
% 0.20/0.58               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.58                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.58                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.58                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.58        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58             ( ~( ![D:$i]:
% 0.20/0.58                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.58                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.58                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.58                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.58        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.58        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('2', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t48_mcart_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58          ( ~( ![D:$i]:
% 0.20/0.58               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.58                 ( ( D ) =
% 0.20/0.58                   ( k3_mcart_1 @
% 0.20/0.58                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.58                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.58                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.58         (((X15) = (k1_xboole_0))
% 0.20/0.58          | ((X16) = (k1_xboole_0))
% 0.20/0.58          | ((X18)
% 0.20/0.58              = (k3_mcart_1 @ (k5_mcart_1 @ X15 @ X16 @ X17 @ X18) @ 
% 0.20/0.58                 (k6_mcart_1 @ X15 @ X16 @ X17 @ X18) @ 
% 0.20/0.58                 (k7_mcart_1 @ X15 @ X16 @ X17 @ X18)))
% 0.20/0.58          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X15 @ X16 @ X17))
% 0.20/0.58          | ((X17) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      ((((sk_C) = (k1_xboole_0))
% 0.20/0.58        | ((sk_D)
% 0.20/0.58            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.58               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.58               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0))
% 0.20/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf('5', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t50_mcart_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.58          ( ~( ![D:$i]:
% 0.20/0.58               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.58                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.58                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.58                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.58                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.58                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.58         (((X22) = (k1_xboole_0))
% 0.20/0.58          | ((X23) = (k1_xboole_0))
% 0.20/0.58          | ((k5_mcart_1 @ X22 @ X23 @ X25 @ X24)
% 0.20/0.58              = (k1_mcart_1 @ (k1_mcart_1 @ X24)))
% 0.20/0.58          | ~ (m1_subset_1 @ X24 @ (k3_zfmisc_1 @ X22 @ X23 @ X25))
% 0.20/0.58          | ((X25) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      ((((sk_C) = (k1_xboole_0))
% 0.20/0.58        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.58            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0))
% 0.20/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('10', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.58         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['7', '8', '9', '10'])).
% 0.20/0.58  thf('12', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.58         (((X22) = (k1_xboole_0))
% 0.20/0.58          | ((X23) = (k1_xboole_0))
% 0.20/0.58          | ((k7_mcart_1 @ X22 @ X23 @ X25 @ X24) = (k2_mcart_1 @ X24))
% 0.20/0.58          | ~ (m1_subset_1 @ X24 @ (k3_zfmisc_1 @ X22 @ X23 @ X25))
% 0.20/0.58          | ((X25) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      ((((sk_C) = (k1_xboole_0))
% 0.20/0.58        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0))
% 0.20/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('16', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('17', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['14', '15', '16', '17'])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      ((((sk_C) = (k1_xboole_0))
% 0.20/0.58        | ((sk_D)
% 0.20/0.58            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.20/0.58               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))
% 0.20/0.58        | ((sk_B) = (k1_xboole_0))
% 0.20/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['4', '11', '18'])).
% 0.20/0.58  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('21', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('22', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (((sk_D)
% 0.20/0.58         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.20/0.58            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      ((((sk_D)
% 0.20/0.58          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ sk_D @ 
% 0.20/0.58             (k2_mcart_1 @ sk_D))))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['1', '23'])).
% 0.20/0.58  thf(t41_mcart_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( k3_zfmisc_1 @
% 0.20/0.58         ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) =
% 0.20/0.58       ( k2_tarski @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) ) ))).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ (k1_tarski @ X11) @ (k2_tarski @ X12 @ X14) @ 
% 0.20/0.58           (k1_tarski @ X13))
% 0.20/0.58           = (k2_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13) @ 
% 0.20/0.58              (k3_mcart_1 @ X11 @ X14 @ X13)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_mcart_1])).
% 0.20/0.58  thf(t69_enumset1, axiom,
% 0.20/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.58  thf('26', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X1) @ 
% 0.20/0.58           (k1_tarski @ X0)) = (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf(t49_mcart_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ~( ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) & 
% 0.20/0.58            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) ) ) & 
% 0.20/0.58            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) ) ) ) =>
% 0.20/0.58       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.58         (((X19) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ X19 @ (k3_zfmisc_1 @ X21 @ X19 @ X20)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t49_mcart_1])).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_tarski @ X1 @ X1) @ 
% 0.20/0.58             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.20/0.58          | ((k2_tarski @ X1 @ X1) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (((~ (r1_tarski @ (k2_tarski @ sk_D @ sk_D) @ (k1_tarski @ sk_D))
% 0.20/0.58         | ((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['24', '29'])).
% 0.20/0.58  thf('31', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.58  thf(l3_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X6 : $i, X7 : $i]:
% 0.20/0.58         ((r1_tarski @ X6 @ (k1_tarski @ X7)) | ((X6) != (k1_tarski @ X7)))),
% 0.20/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X7 : $i]: (r1_tarski @ (k1_tarski @ X7) @ (k1_tarski @ X7))),
% 0.20/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.58  thf('34', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['30', '31', '33', '34'])).
% 0.20/0.58  thf(t65_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.58       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i]:
% 0.20/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.58          | ((k4_xboole_0 @ X9 @ (k1_tarski @ X8)) != (X9)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.20/0.58           | ~ (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf(t3_boole, axiom,
% 0.20/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.58  thf('38', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.58  thf('39', plain,
% 0.20/0.58      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      ((![X0 : $i]: ~ (r2_hidden @ sk_D @ X0))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.58         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['7', '8', '9', '10'])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      ((((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      (((sk_D)
% 0.20/0.58         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.20/0.58            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      ((((sk_D)
% 0.20/0.58          = (k3_mcart_1 @ sk_D @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.58             (k2_mcart_1 @ sk_D))))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X1) @ 
% 0.20/0.58           (k1_tarski @ X0)) = (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.58         (((X19) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ X19 @ (k3_zfmisc_1 @ X19 @ X20 @ X21)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t49_mcart_1])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k1_tarski @ X2) @ 
% 0.20/0.58             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.20/0.58          | ((k1_tarski @ X2) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (((~ (r1_tarski @ (k1_tarski @ sk_D) @ (k1_tarski @ sk_D))
% 0.20/0.58         | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      (![X7 : $i]: (r1_tarski @ (k1_tarski @ X7) @ (k1_tarski @ X7))),
% 0.20/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.58  thf('52', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i]:
% 0.20/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.58          | ((k4_xboole_0 @ X9 @ (k1_tarski @ X8)) != (X9)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.20/0.58           | ~ (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.58  thf('54', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.58  thf('55', plain,
% 0.20/0.58      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      ((![X0 : $i]: ~ (r2_hidden @ sk_D @ X0))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.58  thf(l29_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.20/0.58       ( r2_hidden @ B @ A ) ))).
% 0.20/0.58  thf('58', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         ((r2_hidden @ X3 @ X4)
% 0.20/0.58          | ((k3_xboole_0 @ X4 @ (k1_tarski @ X3)) != (k1_tarski @ X3)))),
% 0.20/0.58      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.20/0.58  thf('59', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_tarski @ sk_D))
% 0.20/0.58           | (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.58  thf(t2_boole, axiom,
% 0.20/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('60', plain,
% 0.20/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.58  thf('63', plain,
% 0.20/0.58      ((![X0 : $i]: (r2_hidden @ sk_D @ X0))
% 0.20/0.58         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.58  thf('64', plain, (~ (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.58      inference('demod', [status(thm)], ['56', '63'])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['14', '15', '16', '17'])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      ((((sk_D) = (k2_mcart_1 @ sk_D)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['65', '66'])).
% 0.20/0.58  thf('68', plain,
% 0.20/0.58      (((sk_D)
% 0.20/0.58         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.20/0.58            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.20/0.58      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.20/0.58  thf('69', plain,
% 0.20/0.58      ((((sk_D)
% 0.20/0.58          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.20/0.58             (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['67', '68'])).
% 0.20/0.58  thf('70', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X1) @ 
% 0.20/0.58           (k1_tarski @ X0)) = (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('71', plain,
% 0.20/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.58         (((X19) = (k1_xboole_0))
% 0.20/0.58          | ~ (r1_tarski @ X19 @ (k3_zfmisc_1 @ X20 @ X21 @ X19)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t49_mcart_1])).
% 0.20/0.58  thf('72', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k1_tarski @ X0) @ 
% 0.20/0.58             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.20/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.58  thf('73', plain,
% 0.20/0.58      (((~ (r1_tarski @ (k1_tarski @ sk_D) @ (k1_tarski @ sk_D))
% 0.20/0.58         | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['69', '72'])).
% 0.20/0.58  thf('74', plain,
% 0.20/0.58      (![X7 : $i]: (r1_tarski @ (k1_tarski @ X7) @ (k1_tarski @ X7))),
% 0.20/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.58  thf('75', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i]:
% 0.20/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.58          | ((k4_xboole_0 @ X9 @ (k1_tarski @ X8)) != (X9)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.58  thf('77', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.20/0.58           | ~ (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.58  thf('78', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.58  thf('79', plain,
% 0.20/0.58      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.58  thf('80', plain,
% 0.20/0.58      ((![X0 : $i]: ~ (r2_hidden @ sk_D @ X0))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['79'])).
% 0.20/0.58  thf('81', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.58  thf('82', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         ((r2_hidden @ X3 @ X4)
% 0.20/0.58          | ((k3_xboole_0 @ X4 @ (k1_tarski @ X3)) != (k1_tarski @ X3)))),
% 0.20/0.58      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.20/0.58  thf('83', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_tarski @ sk_D))
% 0.20/0.58           | (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.58  thf('84', plain,
% 0.20/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('85', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.58  thf('86', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.20/0.58  thf('87', plain,
% 0.20/0.58      ((![X0 : $i]: (r2_hidden @ sk_D @ X0))
% 0.20/0.58         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['86'])).
% 0.20/0.58  thf('88', plain, (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.58      inference('demod', [status(thm)], ['80', '87'])).
% 0.20/0.58  thf('89', plain,
% 0.20/0.58      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.20/0.58       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.20/0.58       (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('90', plain, ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['64', '88', '89'])).
% 0.20/0.58  thf('91', plain, (![X0 : $i]: ~ (r2_hidden @ sk_D @ X0)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['40', '90'])).
% 0.20/0.58  thf('92', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['30', '31', '33', '34'])).
% 0.20/0.58  thf('93', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         ((r2_hidden @ X3 @ X4)
% 0.20/0.58          | ((k3_xboole_0 @ X4 @ (k1_tarski @ X3)) != (k1_tarski @ X3)))),
% 0.20/0.58      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.20/0.58  thf('94', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_tarski @ sk_D))
% 0.20/0.58           | (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.58  thf('95', plain,
% 0.20/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.58  thf('96', plain,
% 0.20/0.58      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['30', '31', '33', '34'])).
% 0.20/0.58  thf('97', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_D @ X0)))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.20/0.58  thf('98', plain,
% 0.20/0.58      ((![X0 : $i]: (r2_hidden @ sk_D @ X0))
% 0.20/0.58         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['97'])).
% 0.20/0.58  thf('99', plain, ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['64', '88', '89'])).
% 0.20/0.58  thf('100', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['98', '99'])).
% 0.20/0.58  thf('101', plain, ($false), inference('demod', [status(thm)], ['91', '100'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
