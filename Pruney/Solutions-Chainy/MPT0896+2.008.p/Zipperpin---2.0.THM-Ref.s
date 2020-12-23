%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vBy15bWGcS

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:39 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  121 (3395 expanded)
%              Number of leaves         :   18 (1049 expanded)
%              Depth                    :   39
%              Number of atoms          : 1245 (57898 expanded)
%              Number of equality atoms :  218 (11163 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

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

thf('0',plain,
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

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( ( k4_zfmisc_1 @ X24 @ X25 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('15',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
       != ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) )
      | ( X17 = X20 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('25',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('28',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['13','25'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
       != ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) )
      | ( X16 = X19 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['13','25'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['39'])).

thf('41',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
       != ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','51'])).

thf('53',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
       != ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_A = X3 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_A = X3 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference(eq_res,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,(
    sk_H = sk_D ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('72',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['69'])).

thf('73',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_C = sk_G ),
    inference(eq_res,[status(thm)],['39'])).

thf('76',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['69'])).

thf('77',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('80',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
       != ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) )
      | ( X16 = X19 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(eq_res,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( sk_B = sk_F ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['69'])).

thf('92',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['69'])).

thf('95',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['74','78','93','94'])).

thf('96',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['70','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['68','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','97'])).

thf('99',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['7','99'])).

thf('101',plain,(
    $false ),
    inference(simplify,[status(thm)],['100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vBy15bWGcS
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 482 iterations in 0.206s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(sk_G_type, type, sk_G: $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.45/0.65  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(sk_H_type, type, sk_H: $i).
% 0.45/0.65  thf(t56_mcart_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.45/0.65     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.45/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.65         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.45/0.66           ( ( D ) = ( H ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.45/0.66        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.45/0.66          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66            ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.45/0.66              ( ( D ) = ( H ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t56_mcart_1])).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.45/0.66         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t55_mcart_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.66         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.45/0.66       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ X24 @ X25 @ X26 @ X27) != (k1_xboole_0))
% 0.45/0.66          | ((X27) = (k1_xboole_0))
% 0.45/0.66          | ((X26) = (k1_xboole_0))
% 0.45/0.66          | ((X25) = (k1_xboole_0))
% 0.45/0.66          | ((X24) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))
% 0.45/0.66        | ((sk_A) = (k1_xboole_0))
% 0.45/0.66        | ((sk_B) = (k1_xboole_0))
% 0.45/0.66        | ((sk_C) = (k1_xboole_0))
% 0.45/0.66        | ((sk_D) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.66  thf('3', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('4', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.45/0.66  thf(d3_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.45/0.66       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.45/0.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.45/0.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.45/0.66      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.66  thf(d4_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.45/0.66       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.66         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.45/0.66           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.45/0.66         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.45/0.66         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf(t37_mcart_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.66     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.45/0.66       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ X15 @ X16 @ X17) = (k1_xboole_0))
% 0.45/0.66          | ((k3_zfmisc_1 @ X15 @ X16 @ X17) != (k3_zfmisc_1 @ X18 @ X19 @ X20))
% 0.45/0.66          | ((X17) = (X20)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((X4) = (X0))
% 0.45/0.66          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.45/0.66            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.45/0.66          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.45/0.66          | ((X0) = (sk_D)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '18'])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.45/0.66            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.45/0.66          | ((X0) = (sk_D))
% 0.45/0.66          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['14', '19'])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.45/0.66            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 0.45/0.66          | ((X0) = (sk_D))
% 0.45/0.66          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.45/0.66        | ((sk_H) = (sk_D)))),
% 0.45/0.66      inference('eq_res', [status(thm)], ['22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.45/0.66  thf('25', plain, (((sk_H) = (sk_D))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.45/0.66         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.66      inference('demod', [status(thm)], ['13', '25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.45/0.66         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.66      inference('demod', [status(thm)], ['13', '25'])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ X15 @ X16 @ X17) = (k1_xboole_0))
% 0.45/0.66          | ((k3_zfmisc_1 @ X15 @ X16 @ X17) != (k3_zfmisc_1 @ X18 @ X19 @ X20))
% 0.45/0.66          | ((X16) = (X19)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.45/0.66          | ((X1) = (X5))
% 0.45/0.66          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.45/0.66          | ((X1) = (X5))
% 0.45/0.66          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.66            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H) = (k1_xboole_0))
% 0.45/0.66          | ((sk_C) = (X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['28', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 0.45/0.66         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.66      inference('demod', [status(thm)], ['13', '25'])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.66            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.45/0.66          | ((sk_C) = (X1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.66            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((sk_C) = (X1)))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.66            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((sk_C) = (X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '38'])).
% 0.45/0.66  thf('40', plain, (((sk_C) = (sk_G))),
% 0.45/0.66      inference('eq_res', [status(thm)], ['39'])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 0.45/0.66         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.66      inference('demod', [status(thm)], ['26', '40'])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ X15 @ X16 @ X17) = (k1_xboole_0))
% 0.45/0.66          | ((k3_zfmisc_1 @ X15 @ X16 @ X17) != (k3_zfmisc_1 @ X18 @ X19 @ X20))
% 0.45/0.66          | ((X15) = (X18)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.45/0.66          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.45/0.66          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.66           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.45/0.66          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 0.45/0.66          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.66            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H) = (k1_xboole_0))
% 0.45/0.66          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['41', '46'])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 0.45/0.66         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.66      inference('demod', [status(thm)], ['26', '40'])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.66            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 0.45/0.66          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.66            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.66            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.66          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['12', '51'])).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.45/0.66      inference('eq_res', [status(thm)], ['52'])).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.45/0.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0)
% 0.45/0.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['53', '54'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.45/0.66           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf(t35_mcart_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.66         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.45/0.66       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ X11 @ X12 @ X13) != (k1_xboole_0))
% 0.45/0.66          | ((X13) = (k1_xboole_0))
% 0.45/0.66          | ((X12) = (k1_xboole_0))
% 0.45/0.66          | ((X11) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k1_xboole_0))
% 0.45/0.66          | ((sk_A) = (k1_xboole_0))
% 0.45/0.66          | ((sk_B) = (k1_xboole_0))
% 0.45/0.66          | ((X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.66  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k1_xboole_0))
% 0.45/0.66          | ((X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['59', '60', '61'])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('64', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ X15 @ X16 @ X17) = (k1_xboole_0))
% 0.45/0.66          | ((k3_zfmisc_1 @ X15 @ X16 @ X17) != (k3_zfmisc_1 @ X18 @ X19 @ X20))
% 0.45/0.66          | ((X15) = (X18)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.45/0.66          | ((sk_A) = (X3))
% 0.45/0.66          | ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.45/0.66          | ((sk_A) = (X3))
% 0.45/0.66          | ((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['65', '66'])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))
% 0.45/0.66          | ((sk_A) = (sk_E)))),
% 0.45/0.66      inference('eq_res', [status(thm)], ['67'])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      ((((sk_A) != (sk_E))
% 0.45/0.66        | ((sk_B) != (sk_F))
% 0.45/0.66        | ((sk_C) != (sk_G))
% 0.45/0.66        | ((sk_D) != (sk_H)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('70', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 0.45/0.66      inference('split', [status(esa)], ['69'])).
% 0.45/0.66  thf('71', plain, (((sk_H) = (sk_D))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.45/0.66  thf('72', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.45/0.66      inference('split', [status(esa)], ['69'])).
% 0.45/0.66  thf('73', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.66  thf('74', plain, ((((sk_D) = (sk_H)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['73'])).
% 0.45/0.66  thf('75', plain, (((sk_C) = (sk_G))),
% 0.45/0.66      inference('eq_res', [status(thm)], ['39'])).
% 0.45/0.66  thf('76', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.45/0.66      inference('split', [status(esa)], ['69'])).
% 0.45/0.66  thf('77', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['75', '76'])).
% 0.45/0.66  thf('78', plain, ((((sk_C) = (sk_G)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['77'])).
% 0.45/0.66  thf('79', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ X15 @ X16 @ X17) = (k1_xboole_0))
% 0.45/0.66          | ((k3_zfmisc_1 @ X15 @ X16 @ X17) != (k3_zfmisc_1 @ X18 @ X19 @ X20))
% 0.45/0.66          | ((X16) = (X19)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.45/0.66          | ((sk_B) = (X2))
% 0.45/0.66          | ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['79', '80'])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 0.45/0.66          | ((sk_B) = (X2))
% 0.45/0.66          | ((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))
% 0.45/0.66          | ((sk_B) = (sk_F)))),
% 0.45/0.66      inference('eq_res', [status(thm)], ['83'])).
% 0.45/0.66  thf('85', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k1_xboole_0))
% 0.45/0.66          | ((X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['59', '60', '61'])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.66          | ((sk_B) = (sk_F))
% 0.45/0.66          | ((X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.66  thf('87', plain, (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['86'])).
% 0.45/0.66  thf('88', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('89', plain, (![X0 : $i]: (((sk_A) != (X0)) | ((sk_B) = (sk_F)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.66  thf('90', plain, (((sk_B) = (sk_F))),
% 0.45/0.66      inference('simplify', [status(thm)], ['89'])).
% 0.45/0.66  thf('91', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.45/0.66      inference('split', [status(esa)], ['69'])).
% 0.45/0.66  thf('92', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['90', '91'])).
% 0.45/0.66  thf('93', plain, ((((sk_B) = (sk_F)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['92'])).
% 0.45/0.66  thf('94', plain,
% 0.45/0.66      (~ (((sk_A) = (sk_E))) | ~ (((sk_B) = (sk_F))) | ~ (((sk_C) = (sk_G))) | 
% 0.45/0.66       ~ (((sk_D) = (sk_H)))),
% 0.45/0.66      inference('split', [status(esa)], ['69'])).
% 0.45/0.66  thf('95', plain, (~ (((sk_A) = (sk_E)))),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['74', '78', '93', '94'])).
% 0.45/0.66  thf('96', plain, (((sk_A) != (sk_E))),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['70', '95'])).
% 0.45/0.66  thf('97', plain,
% 0.45/0.66      (![X0 : $i]: ((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['68', '96'])).
% 0.45/0.66  thf('98', plain,
% 0.45/0.66      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['62', '97'])).
% 0.45/0.66  thf('99', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['98'])).
% 0.45/0.66  thf('100', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['7', '99'])).
% 0.45/0.66  thf('101', plain, ($false), inference('simplify', [status(thm)], ['100'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
