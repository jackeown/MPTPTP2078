%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yExdO9ZZcR

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:38 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 662 expanded)
%              Number of leaves         :   22 ( 206 expanded)
%              Depth                    :   24
%              Number of atoms          : 1493 (10926 expanded)
%              Number of equality atoms :  259 (2169 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) @ X35 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t56_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( D = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( ( A = E )
            & ( B = F )
            & ( C = G )
            & ( D = H ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_mcart_1])).

thf('9',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
       != ( k3_zfmisc_1 @ X29 @ X30 @ X31 ) )
      | ( X26 = X29 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 )
       != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('20',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['27'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X8 @ X7 ) @ ( k2_zfmisc_1 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t36_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X22 @ X21 @ X20 )
       != ( k3_zfmisc_1 @ X23 @ X24 @ X25 ) )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( sk_B = sk_F ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['32','46'])).

thf('48',plain,(
    r1_tarski @ sk_A @ sk_E ),
    inference('sup-',[status(thm)],['1','47'])).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_E @ sk_A )
    | ( sk_E = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('54',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X22 @ X21 @ X20 )
       != ( k3_zfmisc_1 @ X23 @ X24 @ X25 ) )
      | ( X20 = X25 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) @ X1 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('65',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) @ X35 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_E @ sk_F @ X0 @ X1 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference(demod,[status(thm)],['64','70','71'])).

thf('73',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23','24'])).

thf('74',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( X40 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X40 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('77',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','77'])).

thf('79',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23','24'])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ( X38 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X40 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('83',plain,(
    ! [X36: $i,X37: $i,X40: $i] :
      ( ( k4_zfmisc_1 @ X36 @ X37 @ k1_xboole_0 @ X40 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['81','83'])).

thf('85',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23','24'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['51'])).

thf('89',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('94',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
       != ( k3_zfmisc_1 @ X29 @ X30 @ X31 ) )
      | ( X27 = X30 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X5 = X1 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X1 = X5 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4 ) )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X1 = X5 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23','24'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['103'])).

thf('105',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['51'])).

thf('106',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['45'])).

thf('109',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['51'])).

thf('110',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['51'])).

thf('113',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['90','107','111','112'])).

thf('114',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['52','113'])).

thf('115',plain,(
    ~ ( r1_tarski @ sk_E @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['50','114'])).

thf('116',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('117',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('118',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X8 @ X7 ) @ ( k2_zfmisc_1 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

thf('122',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['45'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_F ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    r1_tarski @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['115','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yExdO9ZZcR
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/1.01  % Solved by: fo/fo7.sh
% 0.81/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.01  % done 1215 iterations in 0.554s
% 0.81/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/1.01  % SZS output start Refutation
% 0.81/1.01  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.81/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.81/1.01  thf(sk_E_type, type, sk_E: $i).
% 0.81/1.01  thf(sk_F_type, type, sk_F: $i).
% 0.81/1.01  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.81/1.01  thf(sk_G_type, type, sk_G: $i).
% 0.81/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.01  thf(sk_H_type, type, sk_H: $i).
% 0.81/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.81/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.81/1.01  thf(d10_xboole_0, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.01  thf('0', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.81/1.01      inference('simplify', [status(thm)], ['0'])).
% 0.81/1.01  thf(d3_zfmisc_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.81/1.01       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.81/1.01  thf('2', plain,
% 0.81/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.01         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.81/1.01           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.81/1.01  thf('3', plain,
% 0.81/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.01         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.81/1.01           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.81/1.01  thf('4', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.01         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.01           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.81/1.01      inference('sup+', [status(thm)], ['2', '3'])).
% 0.81/1.01  thf(t53_mcart_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.01     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.81/1.01       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.81/1.01  thf('5', plain,
% 0.81/1.01      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.81/1.01         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 0.81/1.01           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34) @ 
% 0.81/1.01              X35))),
% 0.81/1.01      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.81/1.01  thf('6', plain,
% 0.81/1.01      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.01         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.81/1.01           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.81/1.01      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.81/1.01  thf('7', plain,
% 0.81/1.01      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.81/1.01         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 0.81/1.01           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X32 @ X33 @ X34) @ X35))),
% 0.81/1.01      inference('demod', [status(thm)], ['5', '6'])).
% 0.81/1.01  thf('8', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.01         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.01           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.81/1.01      inference('demod', [status(thm)], ['4', '7'])).
% 0.81/1.01  thf(t56_mcart_1, conjecture,
% 0.81/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.81/1.01     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.81/1.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.81/1.01         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.81/1.01         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.81/1.01           ( ( D ) = ( H ) ) ) ) ))).
% 0.81/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.01    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.81/1.01        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.81/1.01          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.81/1.01            ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.81/1.01            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.81/1.01              ( ( D ) = ( H ) ) ) ) ) )),
% 0.81/1.01    inference('cnf.neg', [status(esa)], [t56_mcart_1])).
% 0.81/1.01  thf('9', plain,
% 0.81/1.01      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.81/1.01         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('10', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.01         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.01           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.81/1.01      inference('demod', [status(thm)], ['4', '7'])).
% 0.81/1.01  thf(t37_mcart_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.81/1.01     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.81/1.01       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.81/1.01         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.81/1.01  thf('11', plain,
% 0.81/1.01      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.81/1.01         (((k3_zfmisc_1 @ X26 @ X27 @ X28) = (k1_xboole_0))
% 0.81/1.01          | ((k3_zfmisc_1 @ X26 @ X27 @ X28) != (k3_zfmisc_1 @ X29 @ X30 @ X31))
% 0.81/1.01          | ((X26) = (X29)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.81/1.01  thf('12', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.01         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.81/1.01          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.81/1.01          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['10', '11'])).
% 0.81/1.01  thf('13', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.01         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.01           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.81/1.01      inference('demod', [status(thm)], ['4', '7'])).
% 0.81/1.01  thf('14', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.01         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.81/1.01          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.81/1.01          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.81/1.01      inference('demod', [status(thm)], ['12', '13'])).
% 0.81/1.01  thf('15', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.01         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.81/1.01            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.81/1.01          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0))
% 0.81/1.01          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['9', '14'])).
% 0.81/1.01  thf('16', plain,
% 0.81/1.01      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.81/1.01         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('17', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.01         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.81/1.01            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.81/1.01          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.81/1.01          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.81/1.01      inference('demod', [status(thm)], ['15', '16'])).
% 0.81/1.01  thf('18', plain,
% 0.81/1.01      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.81/1.01         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(t55_mcart_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.01     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.81/1.01         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.81/1.01       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.81/1.01  thf('19', plain,
% 0.81/1.01      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.81/1.01         (((k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39) != (k1_xboole_0))
% 0.81/1.02          | ((X39) = (k1_xboole_0))
% 0.81/1.02          | ((X38) = (k1_xboole_0))
% 0.81/1.02          | ((X37) = (k1_xboole_0))
% 0.81/1.02          | ((X36) = (k1_xboole_0)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.81/1.02  thf('20', plain,
% 0.81/1.02      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.81/1.02        | ((sk_A) = (k1_xboole_0))
% 0.81/1.02        | ((sk_B) = (k1_xboole_0))
% 0.81/1.02        | ((sk_C) = (k1_xboole_0))
% 0.81/1.02        | ((sk_D) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['18', '19'])).
% 0.81/1.02  thf('21', plain, (((sk_D) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('22', plain, (((sk_C) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('25', plain,
% 0.81/1.02      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)],
% 0.81/1.02                ['20', '21', '22', '23', '24'])).
% 0.81/1.02  thf('26', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.81/1.02            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.81/1.02          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['17', '25'])).
% 0.81/1.02  thf('27', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.81/1.02            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.81/1.02          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['8', '26'])).
% 0.81/1.02  thf('28', plain,
% 0.81/1.02      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.81/1.02      inference('eq_res', [status(thm)], ['27'])).
% 0.81/1.02  thf(t117_zfmisc_1, axiom,
% 0.81/1.02    (![A:$i,B:$i,C:$i]:
% 0.81/1.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.81/1.02          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.81/1.02            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.81/1.02          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.81/1.02  thf('29', plain,
% 0.81/1.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/1.02         (((X7) = (k1_xboole_0))
% 0.81/1.02          | (r1_tarski @ X8 @ X9)
% 0.81/1.02          | ~ (r1_tarski @ (k2_zfmisc_1 @ X8 @ X7) @ (k2_zfmisc_1 @ X9 @ X7)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.81/1.02  thf('30', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_E @ sk_F) @ 
% 0.81/1.02             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.81/1.02          | (r1_tarski @ sk_A @ X0)
% 0.81/1.02          | ((sk_B) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['28', '29'])).
% 0.81/1.02  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('32', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_E @ sk_F) @ 
% 0.81/1.02             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.81/1.02          | (r1_tarski @ sk_A @ X0))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.81/1.02  thf('33', plain,
% 0.81/1.02      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.81/1.02      inference('eq_res', [status(thm)], ['27'])).
% 0.81/1.02  thf('34', plain,
% 0.81/1.02      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.81/1.02           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.81/1.02  thf('35', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0)
% 0.81/1.02           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['33', '34'])).
% 0.81/1.02  thf('36', plain,
% 0.81/1.02      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.81/1.02           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.81/1.02  thf('37', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.81/1.02      inference('demod', [status(thm)], ['35', '36'])).
% 0.81/1.02  thf(t36_mcart_1, axiom,
% 0.81/1.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.81/1.02     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.81/1.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.81/1.02         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.81/1.02         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.81/1.02  thf('38', plain,
% 0.81/1.02      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.81/1.02         (((X20) = (k1_xboole_0))
% 0.81/1.02          | ((X21) = (k1_xboole_0))
% 0.81/1.02          | ((X22) = (k1_xboole_0))
% 0.81/1.02          | ((k3_zfmisc_1 @ X22 @ X21 @ X20) != (k3_zfmisc_1 @ X23 @ X24 @ X25))
% 0.81/1.02          | ((X21) = (X24)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.81/1.02  thf('39', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.81/1.02          | ((sk_B) = (X2))
% 0.81/1.02          | ((sk_A) = (k1_xboole_0))
% 0.81/1.02          | ((sk_B) = (k1_xboole_0))
% 0.81/1.02          | ((X0) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['37', '38'])).
% 0.81/1.02  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('42', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.81/1.02          | ((sk_B) = (X2))
% 0.81/1.02          | ((X0) = (k1_xboole_0)))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['39', '40', '41'])).
% 0.81/1.02  thf('43', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 0.81/1.02      inference('eq_res', [status(thm)], ['42'])).
% 0.81/1.02  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('45', plain, (![X0 : $i]: (((sk_A) != (X0)) | ((sk_B) = (sk_F)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['43', '44'])).
% 0.81/1.02  thf('46', plain, (((sk_B) = (sk_F))),
% 0.81/1.02      inference('simplify', [status(thm)], ['45'])).
% 0.81/1.02  thf('47', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_E @ sk_F) @ 
% 0.81/1.02             (k2_zfmisc_1 @ X0 @ sk_F))
% 0.81/1.02          | (r1_tarski @ sk_A @ X0))),
% 0.81/1.02      inference('demod', [status(thm)], ['32', '46'])).
% 0.81/1.02  thf('48', plain, ((r1_tarski @ sk_A @ sk_E)),
% 0.81/1.02      inference('sup-', [status(thm)], ['1', '47'])).
% 0.81/1.02  thf('49', plain,
% 0.81/1.02      (![X0 : $i, X2 : $i]:
% 0.81/1.02         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.81/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.02  thf('50', plain, ((~ (r1_tarski @ sk_E @ sk_A) | ((sk_E) = (sk_A)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['48', '49'])).
% 0.81/1.02  thf('51', plain,
% 0.81/1.02      ((((sk_A) != (sk_E))
% 0.81/1.02        | ((sk_B) != (sk_F))
% 0.81/1.02        | ((sk_C) != (sk_G))
% 0.81/1.02        | ((sk_D) != (sk_H)))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('52', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.81/1.02      inference('split', [status(esa)], ['51'])).
% 0.81/1.02  thf('53', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.02           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.81/1.02      inference('demod', [status(thm)], ['4', '7'])).
% 0.81/1.02  thf('54', plain,
% 0.81/1.02      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.81/1.02         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('55', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.02           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.81/1.02      inference('demod', [status(thm)], ['4', '7'])).
% 0.81/1.02  thf('56', plain,
% 0.81/1.02      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.81/1.02         (((X20) = (k1_xboole_0))
% 0.81/1.02          | ((X21) = (k1_xboole_0))
% 0.81/1.02          | ((X22) = (k1_xboole_0))
% 0.81/1.02          | ((k3_zfmisc_1 @ X22 @ X21 @ X20) != (k3_zfmisc_1 @ X23 @ X24 @ X25))
% 0.81/1.02          | ((X20) = (X25)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.81/1.02  thf('57', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.02         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.81/1.02          | ((X4) = (X0))
% 0.81/1.02          | ((X6) = (k1_xboole_0))
% 0.81/1.02          | ((X5) = (k1_xboole_0))
% 0.81/1.02          | ((X4) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['55', '56'])).
% 0.81/1.02  thf('58', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.81/1.02            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.81/1.02          | ((X0) = (k1_xboole_0))
% 0.81/1.02          | ((X1) = (k1_xboole_0))
% 0.81/1.02          | ((X2) = (k1_xboole_0))
% 0.81/1.02          | ((X0) = (sk_D)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['54', '57'])).
% 0.81/1.02  thf('59', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.81/1.02            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.81/1.02          | ((X0) = (sk_D))
% 0.81/1.02          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.81/1.02          | ((X1) = (k1_xboole_0))
% 0.81/1.02          | ((X0) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['53', '58'])).
% 0.81/1.02  thf('60', plain,
% 0.81/1.02      ((((sk_H) = (k1_xboole_0))
% 0.81/1.02        | ((sk_G) = (k1_xboole_0))
% 0.81/1.02        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 0.81/1.02        | ((sk_H) = (sk_D)))),
% 0.81/1.02      inference('eq_res', [status(thm)], ['59'])).
% 0.81/1.02  thf('61', plain,
% 0.81/1.02      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.81/1.02           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.81/1.02  thf('62', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.81/1.02          | ((sk_H) = (sk_D))
% 0.81/1.02          | ((sk_G) = (k1_xboole_0))
% 0.81/1.02          | ((sk_H) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['60', '61'])).
% 0.81/1.02  thf('63', plain,
% 0.81/1.02      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.81/1.02           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.81/1.02  thf('64', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (((k3_zfmisc_1 @ k1_xboole_0 @ X0 @ X1)
% 0.81/1.02            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_E @ sk_F @ X0) @ X1))
% 0.81/1.02          | ((sk_H) = (k1_xboole_0))
% 0.81/1.02          | ((sk_G) = (k1_xboole_0))
% 0.81/1.02          | ((sk_H) = (sk_D)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['62', '63'])).
% 0.81/1.02  thf(t113_zfmisc_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.81/1.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.81/1.02  thf('65', plain,
% 0.81/1.02      (![X5 : $i, X6 : $i]:
% 0.81/1.02         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.81/1.02  thf('66', plain,
% 0.81/1.02      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.81/1.02      inference('simplify', [status(thm)], ['65'])).
% 0.81/1.02  thf('67', plain,
% 0.81/1.02      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.81/1.02           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.81/1.02      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.81/1.02  thf('68', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.81/1.02           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.81/1.02      inference('sup+', [status(thm)], ['66', '67'])).
% 0.81/1.02  thf('69', plain,
% 0.81/1.02      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.81/1.02      inference('simplify', [status(thm)], ['65'])).
% 0.81/1.02  thf('70', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.81/1.02      inference('demod', [status(thm)], ['68', '69'])).
% 0.81/1.02  thf('71', plain,
% 0.81/1.02      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.81/1.02         ((k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)
% 0.81/1.02           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X32 @ X33 @ X34) @ X35))),
% 0.81/1.02      inference('demod', [status(thm)], ['5', '6'])).
% 0.81/1.02  thf('72', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_E @ sk_F @ X0 @ X1))
% 0.81/1.02          | ((sk_H) = (k1_xboole_0))
% 0.81/1.02          | ((sk_G) = (k1_xboole_0))
% 0.81/1.02          | ((sk_H) = (sk_D)))),
% 0.81/1.02      inference('demod', [status(thm)], ['64', '70', '71'])).
% 0.81/1.02  thf('73', plain,
% 0.81/1.02      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)],
% 0.81/1.02                ['20', '21', '22', '23', '24'])).
% 0.81/1.02  thf('74', plain,
% 0.81/1.02      ((((k1_xboole_0) != (k1_xboole_0))
% 0.81/1.02        | ((sk_H) = (sk_D))
% 0.81/1.02        | ((sk_G) = (k1_xboole_0))
% 0.81/1.02        | ((sk_H) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['72', '73'])).
% 0.81/1.02  thf('75', plain,
% 0.81/1.02      ((((sk_H) = (k1_xboole_0)) | ((sk_G) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['74'])).
% 0.81/1.02  thf('76', plain,
% 0.81/1.02      (![X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.81/1.02         (((X40) != (k1_xboole_0))
% 0.81/1.02          | ((k4_zfmisc_1 @ X36 @ X37 @ X38 @ X40) = (k1_xboole_0)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.81/1.02  thf('77', plain,
% 0.81/1.02      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.81/1.02         ((k4_zfmisc_1 @ X36 @ X37 @ X38 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.02      inference('simplify', [status(thm)], ['76'])).
% 0.81/1.02  thf('78', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 0.81/1.02          | ((sk_H) = (sk_D))
% 0.81/1.02          | ((sk_G) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['75', '77'])).
% 0.81/1.02  thf('79', plain,
% 0.81/1.02      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)],
% 0.81/1.02                ['20', '21', '22', '23', '24'])).
% 0.81/1.02  thf('80', plain,
% 0.81/1.02      ((((k1_xboole_0) != (k1_xboole_0))
% 0.81/1.02        | ((sk_G) = (k1_xboole_0))
% 0.81/1.02        | ((sk_H) = (sk_D)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['78', '79'])).
% 0.81/1.02  thf('81', plain, ((((sk_H) = (sk_D)) | ((sk_G) = (k1_xboole_0)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['80'])).
% 0.81/1.02  thf('82', plain,
% 0.81/1.02      (![X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.81/1.02         (((X38) != (k1_xboole_0))
% 0.81/1.02          | ((k4_zfmisc_1 @ X36 @ X37 @ X38 @ X40) = (k1_xboole_0)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.81/1.02  thf('83', plain,
% 0.81/1.02      (![X36 : $i, X37 : $i, X40 : $i]:
% 0.81/1.02         ((k4_zfmisc_1 @ X36 @ X37 @ k1_xboole_0 @ X40) = (k1_xboole_0))),
% 0.81/1.02      inference('simplify', [status(thm)], ['82'])).
% 0.81/1.02  thf('84', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0) = (k1_xboole_0))
% 0.81/1.02          | ((sk_H) = (sk_D)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['81', '83'])).
% 0.81/1.02  thf('85', plain,
% 0.81/1.02      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)],
% 0.81/1.02                ['20', '21', '22', '23', '24'])).
% 0.81/1.02  thf('86', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['84', '85'])).
% 0.81/1.02  thf('87', plain, (((sk_H) = (sk_D))),
% 0.81/1.02      inference('simplify', [status(thm)], ['86'])).
% 0.81/1.02  thf('88', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.81/1.02      inference('split', [status(esa)], ['51'])).
% 0.81/1.02  thf('89', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['87', '88'])).
% 0.81/1.02  thf('90', plain, ((((sk_D) = (sk_H)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['89'])).
% 0.81/1.02  thf('91', plain,
% 0.81/1.02      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.81/1.02         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('92', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.02           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.81/1.02      inference('demod', [status(thm)], ['4', '7'])).
% 0.81/1.02  thf('93', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.02           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.81/1.02      inference('demod', [status(thm)], ['4', '7'])).
% 0.81/1.02  thf('94', plain,
% 0.81/1.02      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.81/1.02         (((k3_zfmisc_1 @ X26 @ X27 @ X28) = (k1_xboole_0))
% 0.81/1.02          | ((k3_zfmisc_1 @ X26 @ X27 @ X28) != (k3_zfmisc_1 @ X29 @ X30 @ X31))
% 0.81/1.02          | ((X27) = (X30)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.81/1.02  thf('95', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.81/1.02         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.81/1.02          | ((X5) = (X1))
% 0.81/1.02          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['93', '94'])).
% 0.81/1.02  thf('96', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.81/1.02            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.81/1.02          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0))
% 0.81/1.02          | ((X1) = (X5)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['92', '95'])).
% 0.81/1.02  thf('97', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.81/1.02           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.81/1.02      inference('demod', [status(thm)], ['4', '7'])).
% 0.81/1.02  thf('98', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.81/1.02            != (k4_zfmisc_1 @ X7 @ X6 @ X5 @ X4))
% 0.81/1.02          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.81/1.02          | ((X1) = (X5)))),
% 0.81/1.02      inference('demod', [status(thm)], ['96', '97'])).
% 0.81/1.02  thf('99', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.81/1.02            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.81/1.02          | ((sk_C) = (X1))
% 0.81/1.02          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['91', '98'])).
% 0.81/1.02  thf('100', plain,
% 0.81/1.02      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.81/1.02         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('101', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.81/1.02            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.81/1.02          | ((sk_C) = (X1))
% 0.81/1.02          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0)))),
% 0.81/1.02      inference('demod', [status(thm)], ['99', '100'])).
% 0.81/1.02  thf('102', plain,
% 0.81/1.02      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)],
% 0.81/1.02                ['20', '21', '22', '23', '24'])).
% 0.81/1.02  thf('103', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.81/1.02         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.81/1.02            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.81/1.02          | ((sk_C) = (X1)))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.81/1.02  thf('104', plain, (((sk_C) = (sk_G))),
% 0.81/1.02      inference('eq_res', [status(thm)], ['103'])).
% 0.81/1.02  thf('105', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.81/1.02      inference('split', [status(esa)], ['51'])).
% 0.81/1.02  thf('106', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['104', '105'])).
% 0.81/1.02  thf('107', plain, ((((sk_C) = (sk_G)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['106'])).
% 0.81/1.02  thf('108', plain, (((sk_B) = (sk_F))),
% 0.81/1.02      inference('simplify', [status(thm)], ['45'])).
% 0.81/1.02  thf('109', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.81/1.02      inference('split', [status(esa)], ['51'])).
% 0.81/1.02  thf('110', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['108', '109'])).
% 0.81/1.02  thf('111', plain, ((((sk_B) = (sk_F)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['110'])).
% 0.81/1.02  thf('112', plain,
% 0.81/1.02      (~ (((sk_A) = (sk_E))) | ~ (((sk_B) = (sk_F))) | ~ (((sk_C) = (sk_G))) | 
% 0.81/1.02       ~ (((sk_D) = (sk_H)))),
% 0.81/1.02      inference('split', [status(esa)], ['51'])).
% 0.81/1.02  thf('113', plain, (~ (((sk_A) = (sk_E)))),
% 0.81/1.02      inference('sat_resolution*', [status(thm)], ['90', '107', '111', '112'])).
% 0.81/1.02  thf('114', plain, (((sk_A) != (sk_E))),
% 0.81/1.02      inference('simpl_trail', [status(thm)], ['52', '113'])).
% 0.81/1.02  thf('115', plain, (~ (r1_tarski @ sk_E @ sk_A)),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['50', '114'])).
% 0.81/1.02  thf('116', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.81/1.02      inference('simplify', [status(thm)], ['0'])).
% 0.81/1.02  thf('117', plain,
% 0.81/1.02      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.81/1.02      inference('eq_res', [status(thm)], ['27'])).
% 0.81/1.02  thf('118', plain,
% 0.81/1.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.81/1.02         (((X7) = (k1_xboole_0))
% 0.81/1.02          | (r1_tarski @ X8 @ X9)
% 0.81/1.02          | ~ (r1_tarski @ (k2_zfmisc_1 @ X8 @ X7) @ (k2_zfmisc_1 @ X9 @ X7)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.81/1.02  thf('119', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 0.81/1.02             (k2_zfmisc_1 @ sk_E @ sk_F))
% 0.81/1.02          | (r1_tarski @ X0 @ sk_A)
% 0.81/1.02          | ((sk_B) = (k1_xboole_0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['117', '118'])).
% 0.81/1.02  thf('120', plain, (((sk_B) != (k1_xboole_0))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('121', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 0.81/1.02             (k2_zfmisc_1 @ sk_E @ sk_F))
% 0.81/1.02          | (r1_tarski @ X0 @ sk_A))),
% 0.81/1.02      inference('simplify_reflect-', [status(thm)], ['119', '120'])).
% 0.81/1.02  thf('122', plain, (((sk_B) = (sk_F))),
% 0.81/1.02      inference('simplify', [status(thm)], ['45'])).
% 0.81/1.02  thf('123', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_F) @ 
% 0.81/1.02             (k2_zfmisc_1 @ sk_E @ sk_F))
% 0.81/1.02          | (r1_tarski @ X0 @ sk_A))),
% 0.81/1.02      inference('demod', [status(thm)], ['121', '122'])).
% 0.81/1.02  thf('124', plain, ((r1_tarski @ sk_E @ sk_A)),
% 0.81/1.02      inference('sup-', [status(thm)], ['116', '123'])).
% 0.81/1.02  thf('125', plain, ($false), inference('demod', [status(thm)], ['115', '124'])).
% 0.81/1.02  
% 0.81/1.02  % SZS output end Refutation
% 0.81/1.02  
% 0.81/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
