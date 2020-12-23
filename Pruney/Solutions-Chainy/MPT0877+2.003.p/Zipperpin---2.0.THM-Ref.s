%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cpjUISwH1S

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:21 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  112 (5496 expanded)
%              Number of leaves         :   13 (1433 expanded)
%              Depth                    :   39
%              Number of atoms          :  913 (73088 expanded)
%              Number of equality atoms :  201 (15066 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t37_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = ( k3_zfmisc_1 @ D @ E @ F ) )
       => ( ( ( k3_zfmisc_1 @ A @ B @ C )
            = k1_xboole_0 )
          | ( ( A = D )
            & ( B = E )
            & ( C = F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X8 @ X7 @ X6 )
       != ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) )
      | ( X6 = X11 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_C = X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference(eq_res,[status(thm)],['9'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_C )
        = k1_xboole_0 )
      | ( sk_C = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_F )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','24'])).

thf('26',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup+',[status(thm)],['5','25'])).

thf('27',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup+',[status(thm)],['4','34'])).

thf('36',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('37',plain,(
    sk_C = sk_F ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','37'])).

thf('39',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','37'])).

thf('40',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','37'])).

thf('41',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','37'])).

thf('42',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','37'])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X8 @ X7 @ X6 )
       != ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference(eq_res,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('sup+',[status(thm)],['41','47'])).

thf('49',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('50',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_E )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('sup+',[status(thm)],['40','52'])).

thf('54',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('55',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_B = sk_E ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('sup+',[status(thm)],['39','57'])).

thf('59',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('60',plain,(
    sk_B = sk_E ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_E @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['38','60'])).

thf('62',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_E @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['38','60'])).

thf('63',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_E @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['38','60'])).

thf('64',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X8 @ X7 @ X6 )
       != ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_A = X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(eq_res,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,(
    sk_C = sk_F ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('70',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['67'])).

thf('71',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    sk_B = sk_E ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('74',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['67'])).

thf('75',plain,
    ( ( sk_E != sk_E )
   <= ( sk_B != sk_E ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_B = sk_E ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['67'])).

thf('78',plain,(
    sk_A != sk_D ),
    inference('sat_resolution*',[status(thm)],['72','76','77'])).

thf('79',plain,(
    sk_A != sk_D ),
    inference(simpl_trail,[status(thm)],['68','78'])).

thf('80',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['66','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','82'])).

thf('84',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('85',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','87'])).

thf('89',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('90',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != sk_E ),
    inference(demod,[status(thm)],['2','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('93',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('94',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
      = sk_E ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['91','95'])).

thf('97',plain,(
    $false ),
    inference(simplify,[status(thm)],['96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cpjUISwH1S
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 291 iterations in 0.150s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.60  thf(t37_mcart_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.60     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.39/0.60       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.39/0.60         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.60        ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.39/0.60          ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.39/0.60            ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t37_mcart_1])).
% 0.39/0.60  thf('0', plain, (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('2', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t36_mcart_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.60     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.39/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.60         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.39/0.60         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.60         (((X6) = (k1_xboole_0))
% 0.39/0.60          | ((X7) = (k1_xboole_0))
% 0.39/0.60          | ((X8) = (k1_xboole_0))
% 0.39/0.60          | ((k3_zfmisc_1 @ X8 @ X7 @ X6) != (k3_zfmisc_1 @ X9 @ X10 @ X11))
% 0.39/0.60          | ((X6) = (X11)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.60          | ((sk_C) = (X0))
% 0.39/0.60          | ((sk_A) = (k1_xboole_0))
% 0.39/0.60          | ((sk_B) = (k1_xboole_0))
% 0.39/0.60          | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      ((((sk_C) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B) = (k1_xboole_0))
% 0.39/0.60        | ((sk_A) = (k1_xboole_0))
% 0.39/0.60        | ((sk_C) = (sk_F)))),
% 0.39/0.60      inference('eq_res', [status(thm)], ['9'])).
% 0.39/0.60  thf(t113_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      (![X1 : $i, X2 : $i]:
% 0.39/0.60         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.60  thf(d3_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.39/0.60       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.39/0.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ X1 @ X0 @ sk_C) = (k1_xboole_0))
% 0.39/0.60          | ((sk_C) = (sk_F))
% 0.39/0.60          | ((sk_A) = (k1_xboole_0))
% 0.39/0.60          | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['10', '14'])).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B) = (k1_xboole_0))
% 0.39/0.60        | ((sk_A) = (k1_xboole_0))
% 0.39/0.60        | ((sk_C) = (sk_F)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['6', '15'])).
% 0.39/0.60  thf('17', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('18', plain,
% 0.39/0.60      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.39/0.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.39/0.60           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['19', '20'])).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      (![X1 : $i, X2 : $i]:
% 0.39/0.60         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('23', plain,
% 0.39/0.60      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.60  thf('24', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['21', '23'])).
% 0.39/0.60  thf('25', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ X1 @ sk_B @ X0) = (k1_xboole_0))
% 0.39/0.60          | ((sk_C) = (sk_F))
% 0.39/0.60          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['18', '24'])).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_A) = (k1_xboole_0))
% 0.39/0.60        | ((sk_C) = (sk_F)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['5', '25'])).
% 0.39/0.60  thf('27', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('28', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.39/0.60  thf('29', plain,
% 0.39/0.60      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.60  thf('30', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.39/0.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.60  thf('31', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.39/0.60           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.39/0.60  thf('32', plain,
% 0.39/0.60      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.60  thf('33', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ sk_A @ X1 @ X0) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['28', '33'])).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_C) = (sk_F)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['4', '34'])).
% 0.39/0.60  thf('36', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('37', plain, (((sk_C) = (sk_F))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.39/0.60  thf('38', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('demod', [status(thm)], ['3', '37'])).
% 0.39/0.60  thf('39', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('demod', [status(thm)], ['3', '37'])).
% 0.39/0.60  thf('40', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('demod', [status(thm)], ['3', '37'])).
% 0.39/0.60  thf('41', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('demod', [status(thm)], ['3', '37'])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('demod', [status(thm)], ['3', '37'])).
% 0.39/0.60  thf('43', plain,
% 0.39/0.60      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.60         (((X6) = (k1_xboole_0))
% 0.39/0.60          | ((X7) = (k1_xboole_0))
% 0.39/0.60          | ((X8) = (k1_xboole_0))
% 0.39/0.60          | ((k3_zfmisc_1 @ X8 @ X7 @ X6) != (k3_zfmisc_1 @ X9 @ X10 @ X11))
% 0.39/0.60          | ((X7) = (X10)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.60          | ((sk_B) = (X1))
% 0.39/0.60          | ((sk_A) = (k1_xboole_0))
% 0.39/0.60          | ((sk_B) = (k1_xboole_0))
% 0.39/0.60          | ((sk_F) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('45', plain,
% 0.39/0.60      ((((sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B) = (k1_xboole_0))
% 0.39/0.60        | ((sk_A) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B) = (sk_E)))),
% 0.39/0.60      inference('eq_res', [status(thm)], ['44'])).
% 0.39/0.60  thf('46', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['21', '23'])).
% 0.39/0.60  thf('47', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ X1 @ sk_B @ X0) = (k1_xboole_0))
% 0.39/0.60          | ((sk_B) = (sk_E))
% 0.39/0.60          | ((sk_A) = (k1_xboole_0))
% 0.39/0.60          | ((sk_F) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.60  thf('48', plain,
% 0.39/0.60      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_A) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B) = (sk_E)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['41', '47'])).
% 0.39/0.60  thf('49', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('50', plain,
% 0.39/0.60      ((((sk_F) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_E)))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.39/0.60  thf('51', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.60  thf('52', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.60          | ((sk_B) = (sk_E))
% 0.39/0.60          | ((sk_F) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.60  thf('53', plain,
% 0.39/0.60      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B) = (sk_E)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['40', '52'])).
% 0.39/0.60  thf('54', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('55', plain, ((((sk_F) = (k1_xboole_0)) | ((sk_B) = (sk_E)))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.39/0.60  thf('56', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.60  thf('57', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0)) | ((sk_B) = (sk_E)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['55', '56'])).
% 0.39/0.60  thf('58', plain,
% 0.39/0.60      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B) = (sk_E)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['39', '57'])).
% 0.39/0.60  thf('59', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('60', plain, (((sk_B) = (sk_E))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.39/0.60  thf('61', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_E @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('demod', [status(thm)], ['38', '60'])).
% 0.39/0.60  thf('62', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_E @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('demod', [status(thm)], ['38', '60'])).
% 0.39/0.60  thf('63', plain,
% 0.39/0.60      (((k3_zfmisc_1 @ sk_A @ sk_E @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.60      inference('demod', [status(thm)], ['38', '60'])).
% 0.39/0.60  thf('64', plain,
% 0.39/0.60      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.60         (((X6) = (k1_xboole_0))
% 0.39/0.60          | ((X7) = (k1_xboole_0))
% 0.39/0.60          | ((X8) = (k1_xboole_0))
% 0.39/0.60          | ((k3_zfmisc_1 @ X8 @ X7 @ X6) != (k3_zfmisc_1 @ X9 @ X10 @ X11))
% 0.39/0.60          | ((X8) = (X9)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.39/0.60  thf('65', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.60          | ((sk_A) = (X2))
% 0.39/0.60          | ((sk_A) = (k1_xboole_0))
% 0.39/0.60          | ((sk_E) = (k1_xboole_0))
% 0.39/0.60          | ((sk_F) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.39/0.60  thf('66', plain,
% 0.39/0.60      ((((sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_E) = (k1_xboole_0))
% 0.39/0.60        | ((sk_A) = (k1_xboole_0))
% 0.39/0.60        | ((sk_A) = (sk_D)))),
% 0.39/0.60      inference('eq_res', [status(thm)], ['65'])).
% 0.39/0.60  thf('67', plain,
% 0.39/0.60      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('68', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.39/0.60      inference('split', [status(esa)], ['67'])).
% 0.39/0.60  thf('69', plain, (((sk_C) = (sk_F))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.39/0.60  thf('70', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.39/0.60      inference('split', [status(esa)], ['67'])).
% 0.39/0.60  thf('71', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.60  thf('72', plain, ((((sk_C) = (sk_F)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['71'])).
% 0.39/0.60  thf('73', plain, (((sk_B) = (sk_E))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.39/0.60  thf('74', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.39/0.60      inference('split', [status(esa)], ['67'])).
% 0.39/0.60  thf('75', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.60  thf('76', plain, ((((sk_B) = (sk_E)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['75'])).
% 0.39/0.60  thf('77', plain,
% 0.39/0.60      (~ (((sk_A) = (sk_D))) | ~ (((sk_B) = (sk_E))) | ~ (((sk_C) = (sk_F)))),
% 0.39/0.60      inference('split', [status(esa)], ['67'])).
% 0.39/0.60  thf('78', plain, (~ (((sk_A) = (sk_D)))),
% 0.39/0.60      inference('sat_resolution*', [status(thm)], ['72', '76', '77'])).
% 0.39/0.60  thf('79', plain, (((sk_A) != (sk_D))),
% 0.39/0.60      inference('simpl_trail', [status(thm)], ['68', '78'])).
% 0.39/0.60  thf('80', plain,
% 0.39/0.60      ((((sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_E) = (k1_xboole_0))
% 0.39/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['66', '79'])).
% 0.39/0.60  thf('81', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.60  thf('82', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.60          | ((sk_E) = (k1_xboole_0))
% 0.39/0.60          | ((sk_F) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['80', '81'])).
% 0.39/0.60  thf('83', plain,
% 0.39/0.60      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_E) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['62', '82'])).
% 0.39/0.60  thf('84', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('85', plain, ((((sk_F) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 0.39/0.60  thf('86', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.60  thf('87', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0))
% 0.39/0.60          | ((sk_E) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['85', '86'])).
% 0.39/0.60  thf('88', plain,
% 0.39/0.60      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.39/0.60        | ((sk_E) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['61', '87'])).
% 0.39/0.60  thf('89', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('90', plain, (((sk_E) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.39/0.60  thf('91', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (sk_E))),
% 0.39/0.60      inference('demod', [status(thm)], ['2', '90'])).
% 0.39/0.60  thf('92', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['21', '23'])).
% 0.39/0.60  thf('93', plain, (((sk_E) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.39/0.60  thf('94', plain, (((sk_E) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.39/0.60  thf('95', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (sk_E))),
% 0.39/0.60      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.39/0.60  thf('96', plain, (((sk_E) != (sk_E))),
% 0.39/0.60      inference('demod', [status(thm)], ['91', '95'])).
% 0.39/0.60  thf('97', plain, ($false), inference('simplify', [status(thm)], ['96'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
