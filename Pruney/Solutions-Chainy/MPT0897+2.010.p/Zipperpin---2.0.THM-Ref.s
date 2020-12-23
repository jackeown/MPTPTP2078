%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Mx3qwEo9nW

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:41 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  218 (305780 expanded)
%              Number of leaves         :   18 (83895 expanded)
%              Depth                    :   86
%              Number of atoms          : 2166 (4308892 expanded)
%              Number of equality atoms :  442 (755552 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t57_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
       => ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
            = k1_xboole_0 )
          | ( ( A = E )
            & ( B = F )
            & ( C = G )
            & ( D = H ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_mcart_1])).

thf('0',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
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

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('10',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X20 @ X21 @ X23 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( X23 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

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

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X8 @ X7 )
       != ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X7 = X12 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('29',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) )
      | ( X0 = sk_D )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 ) )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['27','35'])).

thf('37',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_H = sk_D )
      | ( sk_G = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_H = sk_D )
    | ( sk_G = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( X21 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('46',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0 )
        = k1_xboole_0 )
      | ( sk_H = sk_D ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf('48',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_H = sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['8','50'])).

thf('52',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['8','50'])).

thf('53',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['8','50'])).

thf('54',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['8','50'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('56',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['8','50'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('58',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X8 @ X7 )
       != ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X8 = X11 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X1 = X5 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_H = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X1 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference(eq_res,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ X1 @ X0 )
        = ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 ) )
      | ( sk_C = sk_G )
      | ( sk_C = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( sk_C = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('sup+',[status(thm)],['54','66'])).

thf('68',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('69',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_G )
      | ( sk_H = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('sup+',[status(thm)],['53','71'])).

thf('73',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('74',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H )
        = k1_xboole_0 )
      | ( sk_C = sk_G ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
      = k1_xboole_0 )
    | ( sk_C = sk_G ) ),
    inference('sup+',[status(thm)],['52','76'])).

thf('78',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('79',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['51','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('82',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
       != ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) )
      | ( X13 = X16 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = X6 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H )
    = ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['51','79'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = X2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','90'])).

thf('92',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('98',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X8 @ X7 )
       != ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X8 = X11 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_B = X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(eq_res,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B )
      | ( sk_B = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['100'])).

thf('102',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( X20 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('104',plain,(
    ! [X19: $i,X21: $i,X23: $i] :
      ( ( k4_zfmisc_1 @ X19 @ k1_xboole_0 @ X21 @ X23 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['102','109'])).

thf('111',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['91'])).

thf('112',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = sk_F )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('122',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_F )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['91'])).

thf('127',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( sk_B = sk_F ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = sk_F ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = sk_F ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_F ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('137',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_F ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_F @ X0 )
      = ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['96','138'])).

thf('140',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X8 @ X7 )
       != ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X9 = X10 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
       != ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) )
      | ( sk_A = X3 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = sk_E ) ) ),
    inference(eq_res,[status(thm)],['141'])).

thf('143',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( sk_A != sk_E )
   <= ( sk_A != sk_E ) ),
    inference(split,[status(esa)],['143'])).

thf('145',plain,(
    sk_H = sk_D ),
    inference(simplify,[status(thm)],['49'])).

thf('146',plain,
    ( ( sk_D != sk_H )
   <= ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['143'])).

thf('147',plain,
    ( ( sk_H != sk_H )
   <= ( sk_D != sk_H ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    sk_D = sk_H ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_C = sk_G ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('150',plain,
    ( ( sk_C != sk_G )
   <= ( sk_C != sk_G ) ),
    inference(split,[status(esa)],['143'])).

thf('151',plain,
    ( ( sk_G != sk_G )
   <= ( sk_C != sk_G ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    sk_C = sk_G ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['137'])).

thf('154',plain,
    ( ( sk_B != sk_F )
   <= ( sk_B != sk_F ) ),
    inference(split,[status(esa)],['143'])).

thf('155',plain,
    ( ( sk_F != sk_F )
   <= ( sk_B != sk_F ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( sk_A != sk_E )
    | ( sk_B != sk_F )
    | ( sk_C != sk_G )
    | ( sk_D != sk_H ) ),
    inference(split,[status(esa)],['143'])).

thf('158',plain,(
    sk_A != sk_E ),
    inference('sat_resolution*',[status(thm)],['148','152','156','157'])).

thf('159',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['144','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['142','159'])).

thf('161',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['160'])).

thf('162',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['160'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(eq_res,[status(thm)],['91'])).

thf('166',plain,(
    sk_B = sk_F ),
    inference(simplify,[status(thm)],['137'])).

thf('167',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_F )
    = ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_E @ sk_F @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( sk_E = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['175'])).

thf('177',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['175'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['108'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_F )
        = sk_F )
      | ( sk_E = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( sk_E = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ sk_F )
        = sk_F ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_A )
      | ( sk_F = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ sk_F )
        = sk_F ) ) ),
    inference('sup+',[status(thm)],['161','181'])).

thf('183',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['144','158'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( sk_F = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ sk_F )
        = sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['160'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( sk_E = sk_A )
      | ( sk_F = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ sk_F )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    sk_A != sk_E ),
    inference(simpl_trail,[status(thm)],['144','158'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( sk_F = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ sk_F )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_F )
       != sk_F )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['189'])).

thf('191',plain,(
    sk_F = k1_xboole_0 ),
    inference(clc,[status(thm)],['184','190'])).

thf('192',plain,(
    ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H )
 != sk_F ),
    inference(demod,[status(thm)],['2','191'])).

thf('193',plain,(
    ! [X19: $i,X21: $i,X23: $i] :
      ( ( k4_zfmisc_1 @ X19 @ k1_xboole_0 @ X21 @ X23 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('194',plain,(
    sk_F = k1_xboole_0 ),
    inference(clc,[status(thm)],['184','190'])).

thf('195',plain,(
    sk_F = k1_xboole_0 ),
    inference(clc,[status(thm)],['184','190'])).

thf('196',plain,(
    ! [X19: $i,X21: $i,X23: $i] :
      ( ( k4_zfmisc_1 @ X19 @ sk_F @ X21 @ X23 )
      = sk_F ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    sk_F != sk_F ),
    inference(demod,[status(thm)],['192','196'])).

thf('198',plain,(
    $false ),
    inference(simplify,[status(thm)],['197'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Mx3qwEo9nW
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 11:58:20 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.58/1.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.58/1.77  % Solved by: fo/fo7.sh
% 1.58/1.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.58/1.77  % done 1544 iterations in 1.279s
% 1.58/1.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.58/1.77  % SZS output start Refutation
% 1.58/1.77  thf(sk_B_type, type, sk_B: $i).
% 1.58/1.77  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.58/1.77  thf(sk_E_type, type, sk_E: $i).
% 1.58/1.77  thf(sk_F_type, type, sk_F: $i).
% 1.58/1.77  thf(sk_H_type, type, sk_H: $i).
% 1.58/1.77  thf(sk_C_type, type, sk_C: $i).
% 1.58/1.77  thf(sk_A_type, type, sk_A: $i).
% 1.58/1.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.58/1.77  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.58/1.77  thf(sk_G_type, type, sk_G: $i).
% 1.58/1.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.58/1.77  thf(sk_D_type, type, sk_D: $i).
% 1.58/1.77  thf(t57_mcart_1, conjecture,
% 1.58/1.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.58/1.77     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.58/1.77       ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 1.58/1.77         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.58/1.77           ( ( D ) = ( H ) ) ) ) ))).
% 1.58/1.77  thf(zf_stmt_0, negated_conjecture,
% 1.58/1.77    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.58/1.77        ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.58/1.77          ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 1.58/1.77            ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 1.58/1.77              ( ( D ) = ( H ) ) ) ) ) )),
% 1.58/1.77    inference('cnf.neg', [status(esa)], [t57_mcart_1])).
% 1.58/1.77  thf('0', plain,
% 1.58/1.77      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (k1_xboole_0))),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('1', plain,
% 1.58/1.77      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.58/1.77         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('2', plain,
% 1.58/1.77      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.77      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.77  thf(d3_zfmisc_1, axiom,
% 1.58/1.77    (![A:$i,B:$i,C:$i]:
% 1.58/1.77     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.58/1.77       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.58/1.78  thf('3', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 1.58/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.58/1.78  thf('4', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 1.58/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.58/1.78  thf('5', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.58/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.58/1.78      inference('sup+', [status(thm)], ['3', '4'])).
% 1.58/1.78  thf(d4_zfmisc_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i,D:$i]:
% 1.58/1.78     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.58/1.78       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.58/1.78  thf('6', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 1.58/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 1.58/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.58/1.78  thf('7', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('8', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(t55_mcart_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i,D:$i]:
% 1.58/1.78     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.58/1.78         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 1.58/1.78       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 1.58/1.78  thf('9', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.58/1.78         (((X19) != (k1_xboole_0))
% 1.58/1.78          | ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23) = (k1_xboole_0)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.58/1.78  thf('10', plain,
% 1.58/1.78      (![X20 : $i, X21 : $i, X23 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ k1_xboole_0 @ X20 @ X21 @ X23) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['9'])).
% 1.58/1.78  thf('11', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('12', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.58/1.78         (((X23) != (k1_xboole_0))
% 1.58/1.78          | ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23) = (k1_xboole_0)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.58/1.78  thf('13', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['12'])).
% 1.58/1.78  thf('14', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf(t36_mcart_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.58/1.78     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 1.58/1.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.58/1.78         ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.58/1.78         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 1.58/1.78  thf('15', plain,
% 1.58/1.78      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.58/1.78         (((X7) = (k1_xboole_0))
% 1.58/1.78          | ((X8) = (k1_xboole_0))
% 1.58/1.78          | ((X9) = (k1_xboole_0))
% 1.58/1.78          | ((k3_zfmisc_1 @ X9 @ X8 @ X7) != (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 1.58/1.78          | ((X7) = (X12)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t36_mcart_1])).
% 1.58/1.78  thf('16', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.58/1.78          | ((X4) = (X0))
% 1.58/1.78          | ((X6) = (k1_xboole_0))
% 1.58/1.78          | ((X5) = (k1_xboole_0))
% 1.58/1.78          | ((X4) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['14', '15'])).
% 1.58/1.78  thf('17', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k1_xboole_0))
% 1.58/1.78          | ((X3) = (k1_xboole_0))
% 1.58/1.78          | ((X4) = (k1_xboole_0))
% 1.58/1.78          | ((X5) = (k1_xboole_0))
% 1.58/1.78          | ((X3) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['13', '16'])).
% 1.58/1.78  thf('18', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.58/1.78         (((X5) = (k1_xboole_0))
% 1.58/1.78          | ((X4) = (k1_xboole_0))
% 1.58/1.78          | ((X3) = (k1_xboole_0))
% 1.58/1.78          | ((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k1_xboole_0)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['17'])).
% 1.58/1.78  thf('19', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['11', '18'])).
% 1.58/1.78  thf('20', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['10', '19'])).
% 1.58/1.78  thf('21', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((X0) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['20'])).
% 1.58/1.78  thf('22', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0)))),
% 1.58/1.78      inference('condensation', [status(thm)], ['21'])).
% 1.58/1.78  thf('23', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('24', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 1.58/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.58/1.78  thf('25', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 1.58/1.78           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['23', '24'])).
% 1.58/1.78  thf('26', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('27', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['25', '26'])).
% 1.58/1.78  thf('28', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('29', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('30', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.58/1.78          | ((X4) = (X0))
% 1.58/1.78          | ((X6) = (k1_xboole_0))
% 1.58/1.78          | ((X5) = (k1_xboole_0))
% 1.58/1.78          | ((X4) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['14', '15'])).
% 1.58/1.78  thf('31', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 1.58/1.78            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.58/1.78          | ((X0) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((X2) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (sk_D)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['29', '30'])).
% 1.58/1.78  thf('32', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78            != (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))
% 1.58/1.78          | ((X0) = (sk_D))
% 1.58/1.78          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['28', '31'])).
% 1.58/1.78  thf('33', plain,
% 1.58/1.78      ((((sk_H) = (k1_xboole_0))
% 1.58/1.78        | ((sk_G) = (k1_xboole_0))
% 1.58/1.78        | ((k2_zfmisc_1 @ sk_E @ sk_F) = (k1_xboole_0))
% 1.58/1.78        | ((sk_H) = (sk_D)))),
% 1.58/1.78      inference('eq_res', [status(thm)], ['32'])).
% 1.58/1.78  thf('34', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('35', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)
% 1.58/1.78            = (k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0))
% 1.58/1.78          | ((sk_H) = (sk_D))
% 1.58/1.78          | ((sk_G) = (k1_xboole_0))
% 1.58/1.78          | ((sk_H) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['33', '34'])).
% 1.58/1.78  thf('36', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_H) = (k1_xboole_0))
% 1.58/1.78          | ((sk_G) = (k1_xboole_0))
% 1.58/1.78          | ((sk_H) = (sk_D)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['27', '35'])).
% 1.58/1.78  thf('37', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('38', plain,
% 1.58/1.78      ((((k1_xboole_0) != (k1_xboole_0))
% 1.58/1.78        | ((sk_H) = (sk_D))
% 1.58/1.78        | ((sk_G) = (k1_xboole_0))
% 1.58/1.78        | ((sk_H) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['36', '37'])).
% 1.58/1.78  thf('39', plain,
% 1.58/1.78      ((((sk_H) = (k1_xboole_0)) | ((sk_G) = (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['38'])).
% 1.58/1.78  thf('40', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['12'])).
% 1.58/1.78  thf('41', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 1.58/1.78          | ((sk_H) = (sk_D))
% 1.58/1.78          | ((sk_G) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['39', '40'])).
% 1.58/1.78  thf('42', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('43', plain,
% 1.58/1.78      ((((k1_xboole_0) != (k1_xboole_0))
% 1.58/1.78        | ((sk_G) = (k1_xboole_0))
% 1.58/1.78        | ((sk_H) = (sk_D)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['41', '42'])).
% 1.58/1.78  thf('44', plain, ((((sk_H) = (sk_D)) | ((sk_G) = (k1_xboole_0)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['43'])).
% 1.58/1.78  thf('45', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.58/1.78         (((X21) != (k1_xboole_0))
% 1.58/1.78          | ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23) = (k1_xboole_0)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.58/1.78  thf('46', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X23 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X19 @ X20 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['45'])).
% 1.58/1.78  thf('47', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ sk_G @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_H) = (sk_D)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['44', '46'])).
% 1.58/1.78  thf('48', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('49', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_H) = (sk_D)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['47', '48'])).
% 1.58/1.78  thf('50', plain, (((sk_H) = (sk_D))),
% 1.58/1.78      inference('simplify', [status(thm)], ['49'])).
% 1.58/1.78  thf('51', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('demod', [status(thm)], ['8', '50'])).
% 1.58/1.78  thf('52', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('demod', [status(thm)], ['8', '50'])).
% 1.58/1.78  thf('53', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('demod', [status(thm)], ['8', '50'])).
% 1.58/1.78  thf('54', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('demod', [status(thm)], ['8', '50'])).
% 1.58/1.78  thf('55', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('56', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_H)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('demod', [status(thm)], ['8', '50'])).
% 1.58/1.78  thf('57', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('58', plain,
% 1.58/1.78      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.58/1.78         (((X7) = (k1_xboole_0))
% 1.58/1.78          | ((X8) = (k1_xboole_0))
% 1.58/1.78          | ((X9) = (k1_xboole_0))
% 1.58/1.78          | ((k3_zfmisc_1 @ X9 @ X8 @ X7) != (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 1.58/1.78          | ((X8) = (X11)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t36_mcart_1])).
% 1.58/1.78  thf('59', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.58/1.78          | ((X1) = (X5))
% 1.58/1.78          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['57', '58'])).
% 1.58/1.78  thf('60', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.58/1.78            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.58/1.78          | ((sk_H) = (k1_xboole_0))
% 1.58/1.78          | ((sk_C) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.58/1.78          | ((sk_C) = (X1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['56', '59'])).
% 1.58/1.78  thf('61', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.58/1.78            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.58/1.78          | ((sk_C) = (X1))
% 1.58/1.78          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.58/1.78          | ((sk_C) = (k1_xboole_0))
% 1.58/1.78          | ((sk_H) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['55', '60'])).
% 1.58/1.78  thf('62', plain,
% 1.58/1.78      ((((sk_H) = (k1_xboole_0))
% 1.58/1.78        | ((sk_C) = (k1_xboole_0))
% 1.58/1.78        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.58/1.78        | ((sk_C) = (sk_G)))),
% 1.58/1.78      inference('eq_res', [status(thm)], ['61'])).
% 1.58/1.78  thf('63', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('64', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_A @ sk_B @ X1 @ X0)
% 1.58/1.78            = (k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0))
% 1.58/1.78          | ((sk_C) = (sk_G))
% 1.58/1.78          | ((sk_C) = (k1_xboole_0))
% 1.58/1.78          | ((sk_H) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['62', '63'])).
% 1.58/1.78  thf('65', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['25', '26'])).
% 1.58/1.78  thf('66', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_A @ sk_B @ X1 @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_C) = (sk_G))
% 1.58/1.78          | ((sk_C) = (k1_xboole_0))
% 1.58/1.78          | ((sk_H) = (k1_xboole_0)))),
% 1.58/1.78      inference('demod', [status(thm)], ['64', '65'])).
% 1.58/1.78  thf('67', plain,
% 1.58/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.58/1.78        | ((sk_H) = (k1_xboole_0))
% 1.58/1.78        | ((sk_C) = (k1_xboole_0))
% 1.58/1.78        | ((sk_C) = (sk_G)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['54', '66'])).
% 1.58/1.78  thf('68', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('69', plain,
% 1.58/1.78      ((((sk_H) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.58/1.78  thf('70', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X23 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X19 @ X20 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['45'])).
% 1.58/1.78  thf('71', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ sk_C @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_C) = (sk_G))
% 1.58/1.78          | ((sk_H) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['69', '70'])).
% 1.58/1.78  thf('72', plain,
% 1.58/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.58/1.78        | ((sk_H) = (k1_xboole_0))
% 1.58/1.78        | ((sk_C) = (sk_G)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['53', '71'])).
% 1.58/1.78  thf('73', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('74', plain, ((((sk_H) = (k1_xboole_0)) | ((sk_C) = (sk_G)))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 1.58/1.78  thf('75', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['12'])).
% 1.58/1.78  thf('76', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H) = (k1_xboole_0))
% 1.58/1.78          | ((sk_C) = (sk_G)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['74', '75'])).
% 1.58/1.78  thf('77', plain,
% 1.58/1.78      ((((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.58/1.78        | ((sk_C) = (sk_G)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['52', '76'])).
% 1.58/1.78  thf('78', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('79', plain, (((sk_C) = (sk_G))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 1.58/1.78  thf('80', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('demod', [status(thm)], ['51', '79'])).
% 1.58/1.78  thf('81', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf(t37_mcart_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.58/1.78     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 1.58/1.78       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 1.58/1.78         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 1.58/1.78  thf('82', plain,
% 1.58/1.78      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ X13 @ X14 @ X15) = (k1_xboole_0))
% 1.58/1.78          | ((k3_zfmisc_1 @ X13 @ X14 @ X15) != (k3_zfmisc_1 @ X16 @ X17 @ X18))
% 1.58/1.78          | ((X13) = (X16)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t37_mcart_1])).
% 1.58/1.78  thf('83', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.58/1.78          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 1.58/1.78          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['81', '82'])).
% 1.58/1.78  thf('84', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 1.58/1.78           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '6'])).
% 1.58/1.78  thf('85', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 1.58/1.78          | ((k2_zfmisc_1 @ X3 @ X2) = (X6))
% 1.58/1.78          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 1.58/1.78      inference('demod', [status(thm)], ['83', '84'])).
% 1.58/1.78  thf('86', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.58/1.78            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.58/1.78          | ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['80', '85'])).
% 1.58/1.78  thf('87', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_G @ sk_H)
% 1.58/1.78         = (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.58/1.78      inference('demod', [status(thm)], ['51', '79'])).
% 1.58/1.78  thf('88', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.58/1.78            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.58/1.78          | ((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 1.58/1.78      inference('demod', [status(thm)], ['86', '87'])).
% 1.58/1.78  thf('89', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('90', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.58/1.78            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.58/1.78          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (X2)))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 1.58/1.78  thf('91', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H)
% 1.58/1.78            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 1.58/1.78          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ X3 @ X2)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['7', '90'])).
% 1.58/1.78  thf('92', plain,
% 1.58/1.78      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 1.58/1.78      inference('eq_res', [status(thm)], ['91'])).
% 1.58/1.78  thf('93', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 1.58/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.58/1.78  thf('94', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['92', '93'])).
% 1.58/1.78  thf('95', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 1.58/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.58/1.78  thf('96', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['94', '95'])).
% 1.58/1.78  thf('97', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['94', '95'])).
% 1.58/1.78  thf('98', plain,
% 1.58/1.78      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.58/1.78         (((X7) = (k1_xboole_0))
% 1.58/1.78          | ((X8) = (k1_xboole_0))
% 1.58/1.78          | ((X9) = (k1_xboole_0))
% 1.58/1.78          | ((k3_zfmisc_1 @ X9 @ X8 @ X7) != (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 1.58/1.78          | ((X8) = (X11)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t36_mcart_1])).
% 1.58/1.78  thf('99', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 1.58/1.78          | ((sk_B) = (X2))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['97', '98'])).
% 1.58/1.78  thf('100', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (k1_xboole_0))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('eq_res', [status(thm)], ['99'])).
% 1.58/1.78  thf('101', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((X0) != (sk_B))
% 1.58/1.78          | ((sk_B) = (sk_F))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (k1_xboole_0)))),
% 1.58/1.78      inference('eq_fact', [status(thm)], ['100'])).
% 1.58/1.78  thf('102', plain,
% 1.58/1.78      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['101'])).
% 1.58/1.78  thf('103', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.58/1.78         (((X20) != (k1_xboole_0))
% 1.58/1.78          | ((k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23) = (k1_xboole_0)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.58/1.78  thf('104', plain,
% 1.58/1.78      (![X19 : $i, X21 : $i, X23 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X19 @ k1_xboole_0 @ X21 @ X23) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['103'])).
% 1.58/1.78  thf('105', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['11', '18'])).
% 1.58/1.78  thf('106', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['104', '105'])).
% 1.58/1.78  thf('107', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (((X0) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['106'])).
% 1.58/1.78  thf('108', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.58/1.78          | ((X1) = (k1_xboole_0)))),
% 1.58/1.78      inference('condensation', [status(thm)], ['107'])).
% 1.58/1.78  thf('109', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['108'])).
% 1.58/1.78  thf('110', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (sk_F))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['102', '109'])).
% 1.58/1.78  thf('111', plain,
% 1.58/1.78      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 1.58/1.78      inference('eq_res', [status(thm)], ['91'])).
% 1.58/1.78  thf('112', plain,
% 1.58/1.78      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 1.58/1.78        | ((sk_A) = (k1_xboole_0))
% 1.58/1.78        | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['110', '111'])).
% 1.58/1.78  thf('113', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 1.58/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.58/1.78  thf('114', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.58/1.78          | ((sk_B) = (sk_F))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['112', '113'])).
% 1.58/1.78  thf('115', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('116', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (sk_F))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0)))),
% 1.58/1.78      inference('demod', [status(thm)], ['114', '115'])).
% 1.58/1.78  thf('117', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 1.58/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 1.58/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.58/1.78  thf('118', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)
% 1.58/1.78            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['116', '117'])).
% 1.58/1.78  thf('119', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('120', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('demod', [status(thm)], ['118', '119'])).
% 1.58/1.78  thf('121', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('122', plain,
% 1.58/1.78      ((((k1_xboole_0) != (k1_xboole_0))
% 1.58/1.78        | ((sk_B) = (sk_F))
% 1.58/1.78        | ((sk_A) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['120', '121'])).
% 1.58/1.78  thf('123', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['122'])).
% 1.58/1.78  thf('124', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('125', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['123', '124'])).
% 1.58/1.78  thf('126', plain,
% 1.58/1.78      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 1.58/1.78      inference('eq_res', [status(thm)], ['91'])).
% 1.58/1.78  thf('127', plain,
% 1.58/1.78      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_E @ sk_F)) | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['125', '126'])).
% 1.58/1.78  thf('128', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 1.58/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.58/1.78  thf('129', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.58/1.78          | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['127', '128'])).
% 1.58/1.78  thf('130', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('131', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('demod', [status(thm)], ['129', '130'])).
% 1.58/1.78  thf('132', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 1.58/1.78           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 1.58/1.78      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.58/1.78  thf('133', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0)
% 1.58/1.78            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.58/1.78          | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['131', '132'])).
% 1.58/1.78  thf('134', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('135', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k4_zfmisc_1 @ sk_E @ sk_F @ X1 @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('demod', [status(thm)], ['133', '134'])).
% 1.58/1.78  thf('136', plain,
% 1.58/1.78      (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.58/1.78  thf('137', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (sk_F)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['135', '136'])).
% 1.58/1.78  thf('138', plain, (((sk_B) = (sk_F))),
% 1.58/1.78      inference('simplify', [status(thm)], ['137'])).
% 1.58/1.78  thf('139', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ sk_A @ sk_F @ X0) = (k3_zfmisc_1 @ sk_E @ sk_F @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['96', '138'])).
% 1.58/1.78  thf('140', plain,
% 1.58/1.78      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.58/1.78         (((X7) = (k1_xboole_0))
% 1.58/1.78          | ((X8) = (k1_xboole_0))
% 1.58/1.78          | ((X9) = (k1_xboole_0))
% 1.58/1.78          | ((k3_zfmisc_1 @ X9 @ X8 @ X7) != (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 1.58/1.78          | ((X9) = (X10)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t36_mcart_1])).
% 1.58/1.78  thf('141', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) != (k3_zfmisc_1 @ X3 @ X2 @ X1))
% 1.58/1.78          | ((sk_A) = (X3))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['139', '140'])).
% 1.58/1.78  thf('142', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0))
% 1.58/1.78          | ((sk_A) = (sk_E)))),
% 1.58/1.78      inference('eq_res', [status(thm)], ['141'])).
% 1.58/1.78  thf('143', plain,
% 1.58/1.78      ((((sk_A) != (sk_E))
% 1.58/1.78        | ((sk_B) != (sk_F))
% 1.58/1.78        | ((sk_C) != (sk_G))
% 1.58/1.78        | ((sk_D) != (sk_H)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('144', plain, ((((sk_A) != (sk_E))) <= (~ (((sk_A) = (sk_E))))),
% 1.58/1.78      inference('split', [status(esa)], ['143'])).
% 1.58/1.78  thf('145', plain, (((sk_H) = (sk_D))),
% 1.58/1.78      inference('simplify', [status(thm)], ['49'])).
% 1.58/1.78  thf('146', plain, ((((sk_D) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 1.58/1.78      inference('split', [status(esa)], ['143'])).
% 1.58/1.78  thf('147', plain, ((((sk_H) != (sk_H))) <= (~ (((sk_D) = (sk_H))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['145', '146'])).
% 1.58/1.78  thf('148', plain, ((((sk_D) = (sk_H)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['147'])).
% 1.58/1.78  thf('149', plain, (((sk_C) = (sk_G))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 1.58/1.78  thf('150', plain, ((((sk_C) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 1.58/1.78      inference('split', [status(esa)], ['143'])).
% 1.58/1.78  thf('151', plain, ((((sk_G) != (sk_G))) <= (~ (((sk_C) = (sk_G))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['149', '150'])).
% 1.58/1.78  thf('152', plain, ((((sk_C) = (sk_G)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['151'])).
% 1.58/1.78  thf('153', plain, (((sk_B) = (sk_F))),
% 1.58/1.78      inference('simplify', [status(thm)], ['137'])).
% 1.58/1.78  thf('154', plain, ((((sk_B) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 1.58/1.78      inference('split', [status(esa)], ['143'])).
% 1.58/1.78  thf('155', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_B) = (sk_F))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['153', '154'])).
% 1.58/1.78  thf('156', plain, ((((sk_B) = (sk_F)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['155'])).
% 1.58/1.78  thf('157', plain,
% 1.58/1.78      (~ (((sk_A) = (sk_E))) | ~ (((sk_B) = (sk_F))) | ~ (((sk_C) = (sk_G))) | 
% 1.58/1.78       ~ (((sk_D) = (sk_H)))),
% 1.58/1.78      inference('split', [status(esa)], ['143'])).
% 1.58/1.78  thf('158', plain, (~ (((sk_A) = (sk_E)))),
% 1.58/1.78      inference('sat_resolution*', [status(thm)], ['148', '152', '156', '157'])).
% 1.58/1.78  thf('159', plain, (((sk_A) != (sk_E))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['144', '158'])).
% 1.58/1.78  thf('160', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((sk_A) = (k1_xboole_0)))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['142', '159'])).
% 1.58/1.78  thf('161', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('condensation', [status(thm)], ['160'])).
% 1.58/1.78  thf('162', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('condensation', [status(thm)], ['160'])).
% 1.58/1.78  thf('163', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('164', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['162', '163'])).
% 1.58/1.78  thf('165', plain,
% 1.58/1.78      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 1.58/1.78      inference('eq_res', [status(thm)], ['91'])).
% 1.58/1.78  thf('166', plain, (((sk_B) = (sk_F))),
% 1.58/1.78      inference('simplify', [status(thm)], ['137'])).
% 1.58/1.78  thf('167', plain,
% 1.58/1.78      (((k2_zfmisc_1 @ sk_A @ sk_F) = (k2_zfmisc_1 @ sk_E @ sk_F))),
% 1.58/1.78      inference('demod', [status(thm)], ['165', '166'])).
% 1.58/1.78  thf('168', plain,
% 1.58/1.78      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_E @ sk_F))
% 1.58/1.78        | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['164', '167'])).
% 1.58/1.78  thf('169', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 1.58/1.78           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 1.58/1.78      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.58/1.78  thf('170', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['168', '169'])).
% 1.58/1.78  thf('171', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['22'])).
% 1.58/1.78  thf('172', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k3_zfmisc_1 @ sk_E @ sk_F @ X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('demod', [status(thm)], ['170', '171'])).
% 1.58/1.78  thf('173', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.58/1.78         (((X5) = (k1_xboole_0))
% 1.58/1.78          | ((X4) = (k1_xboole_0))
% 1.58/1.78          | ((X3) = (k1_xboole_0))
% 1.58/1.78          | ((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k1_xboole_0)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['17'])).
% 1.58/1.78  thf('174', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((sk_E) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['172', '173'])).
% 1.58/1.78  thf('175', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((sk_E) = (k1_xboole_0))
% 1.58/1.78          | ((X0) = (k1_xboole_0))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['174'])).
% 1.58/1.78  thf('176', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('condensation', [status(thm)], ['175'])).
% 1.58/1.78  thf('177', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('condensation', [status(thm)], ['175'])).
% 1.58/1.78  thf('178', plain,
% 1.58/1.78      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('condensation', [status(thm)], ['108'])).
% 1.58/1.78  thf('179', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ X0 @ sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((sk_E) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['177', '178'])).
% 1.58/1.78  thf('180', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ X0 @ sk_F) = (sk_F))
% 1.58/1.78          | ((sk_E) = (k1_xboole_0))
% 1.58/1.78          | ((sk_E) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['176', '179'])).
% 1.58/1.78  thf('181', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((sk_E) = (k1_xboole_0)) | ((k2_zfmisc_1 @ X0 @ sk_F) = (sk_F)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['180'])).
% 1.58/1.78  thf('182', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((sk_E) = (sk_A))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ X0 @ sk_F) = (sk_F)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['161', '181'])).
% 1.58/1.78  thf('183', plain, (((sk_A) != (sk_E))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['144', '158'])).
% 1.58/1.78  thf('184', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((sk_F) = (k1_xboole_0)) | ((k2_zfmisc_1 @ X0 @ sk_F) = (sk_F)))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['182', '183'])).
% 1.58/1.78  thf('185', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('condensation', [status(thm)], ['160'])).
% 1.58/1.78  thf('186', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ X0 @ sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((sk_E) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['177', '178'])).
% 1.58/1.78  thf('187', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((sk_E) = (sk_A))
% 1.58/1.78          | ((sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ X0 @ sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['185', '186'])).
% 1.58/1.78  thf('188', plain, (((sk_A) != (sk_E))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['144', '158'])).
% 1.58/1.78  thf('189', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((sk_F) = (k1_xboole_0))
% 1.58/1.78          | ((k2_zfmisc_1 @ X0 @ sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['187', '188'])).
% 1.58/1.78  thf('190', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ X0 @ sk_F) != (sk_F)) | ((sk_F) = (k1_xboole_0)))),
% 1.58/1.78      inference('eq_fact', [status(thm)], ['189'])).
% 1.58/1.78  thf('191', plain, (((sk_F) = (k1_xboole_0))),
% 1.58/1.78      inference('clc', [status(thm)], ['184', '190'])).
% 1.58/1.78  thf('192', plain, (((k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H) != (sk_F))),
% 1.58/1.78      inference('demod', [status(thm)], ['2', '191'])).
% 1.58/1.78  thf('193', plain,
% 1.58/1.78      (![X19 : $i, X21 : $i, X23 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X19 @ k1_xboole_0 @ X21 @ X23) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['103'])).
% 1.58/1.78  thf('194', plain, (((sk_F) = (k1_xboole_0))),
% 1.58/1.78      inference('clc', [status(thm)], ['184', '190'])).
% 1.58/1.78  thf('195', plain, (((sk_F) = (k1_xboole_0))),
% 1.58/1.78      inference('clc', [status(thm)], ['184', '190'])).
% 1.58/1.78  thf('196', plain,
% 1.58/1.78      (![X19 : $i, X21 : $i, X23 : $i]:
% 1.58/1.78         ((k4_zfmisc_1 @ X19 @ sk_F @ X21 @ X23) = (sk_F))),
% 1.58/1.78      inference('demod', [status(thm)], ['193', '194', '195'])).
% 1.58/1.78  thf('197', plain, (((sk_F) != (sk_F))),
% 1.58/1.78      inference('demod', [status(thm)], ['192', '196'])).
% 1.58/1.78  thf('198', plain, ($false), inference('simplify', [status(thm)], ['197'])).
% 1.58/1.78  
% 1.58/1.78  % SZS output end Refutation
% 1.58/1.78  
% 1.58/1.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
