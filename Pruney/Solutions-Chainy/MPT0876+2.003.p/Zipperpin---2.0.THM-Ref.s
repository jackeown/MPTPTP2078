%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GTT7PbsE1k

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  168 (7055 expanded)
%              Number of leaves         :   13 (1909 expanded)
%              Depth                    :   58
%              Number of atoms          : 1443 (96752 expanded)
%              Number of equality atoms :  359 (23411 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t36_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = ( k3_zfmisc_1 @ D @ E @ F ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( ( A = D )
            & ( B = E )
            & ( C = F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_mcart_1])).

thf('0',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X4
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['13'])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('17',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X3 = X0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      | ( X0 = sk_C )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_F = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_F = sk_C )
      | ( sk_D = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_F = sk_C )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_F = sk_C ) ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_D = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('58',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_F = sk_C ) ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_F = sk_C ),
    inference('simplify_reflect-',[status(thm)],['68','69','70'])).

thf('72',plain,(
    sk_F != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','71'])).

thf('73',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','72'])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_A = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_A = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( sk_A = sk_D )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','45'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_D )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_A = sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('97',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    sk_A = sk_D ),
    inference('simplify_reflect-',[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','104'])).

thf('106',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','72'])).

thf('107',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_B = X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( sk_B = sk_E )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['111'])).

thf('113',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,(
    sk_F = sk_C ),
    inference('simplify_reflect-',[status(thm)],['68','69','70'])).

thf('116',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['113'])).

thf('117',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    sk_A = sk_D ),
    inference('simplify_reflect-',[status(thm)],['101','102','103'])).

thf('120',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['113'])).

thf('121',plain,
    ( ( sk_D != sk_D )
   <= ( sk_A != sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( sk_B != sk_E )
    | ( sk_A != sk_D )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['113'])).

thf('124',plain,(
    sk_B != sk_E ),
    inference('sat_resolution*',[status(thm)],['118','122','123'])).

thf('125',plain,(
    sk_B != sk_E ),
    inference(simpl_trail,[status(thm)],['114','124'])).

thf('126',plain,
    ( ( k2_zfmisc_1 @ sk_D @ sk_E )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['112','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('128',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    sk_A = sk_D ),
    inference('simplify_reflect-',[status(thm)],['101','102','103'])).

thf('132',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

thf('134',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

thf('135',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != sk_E )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = sk_E ) ),
    inference(demod,[status(thm)],['105','133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','45'])).

thf('137',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

thf('138',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
      = sk_E ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = sk_E ) ),
    inference(demod,[status(thm)],['135','139'])).

thf('141',plain,
    ( ( k2_zfmisc_1 @ sk_D @ sk_B )
    = sk_E ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('143',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

thf('144',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

thf('145',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_E )
      | ( X1 = sk_E )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != sk_E ) ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,
    ( ( sk_E != sk_E )
    | ( sk_D = sk_E )
    | ( sk_B = sk_E ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,
    ( ( sk_B = sk_E )
    | ( sk_D = sk_E ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['130','131'])).

thf('150',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

thf('151',plain,(
    sk_D != sk_E ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    sk_B != sk_E ),
    inference(simpl_trail,[status(thm)],['114','124'])).

thf('153',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['148','151','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GTT7PbsE1k
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 260 iterations in 0.096s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(t36_mcart_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.54     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.54        ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.54          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54            ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54            ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t36_mcart_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d3_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf(t113_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.54          | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.54        | ((sk_C) = (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.54  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf(t134_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (((X3) = (k1_xboole_0))
% 0.20/0.54          | ((X4) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.54          | ((X4) = (X5)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X4 @ X3) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.54          | ((X4) = (k2_zfmisc_1 @ X2 @ X1))
% 0.20/0.54          | ((X4) = (k1_xboole_0))
% 0.20/0.54          | ((X3) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X1 @ X0) != (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.54          | ((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.54          | ((k2_zfmisc_1 @ X2 @ X1) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.54          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.54          | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      ((((sk_F) = (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('eq_res', [status(thm)], ['13'])).
% 0.20/0.54  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (((X3) = (k1_xboole_0))
% 0.20/0.54          | ((X4) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.54          | ((X3) = (X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X4 @ X3) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.54          | ((X3) = (X0))
% 0.20/0.54          | ((X4) = (k1_xboole_0))
% 0.20/0.54          | ((X3) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X1 @ X0) != (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.54          | ((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((X0) = (sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.54          | ((X0) = (sk_C))
% 0.20/0.54          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.54          | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((((sk_F) = (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('eq_res', [status(thm)], ['22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((sk_F) = (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((((sk_E) = (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['27', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0))
% 0.20/0.54          | ((sk_F) = (sk_C))
% 0.20/0.54          | ((sk_D) = (k1_xboole_0))
% 0.20/0.54          | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['26', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_E) = (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_E) = (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.54  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      ((((sk_F) = (sk_C)) | ((sk_D) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.20/0.54           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (k1_xboole_0))
% 0.20/0.54          | ((sk_D) = (k1_xboole_0))
% 0.20/0.54          | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['40', '46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.54  thf('54', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('55', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('56', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['53', '54', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.20/0.54           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k3_zfmisc_1 @ sk_D @ X1 @ X0) = (k1_xboole_0)) | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['56', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['64'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_F) = (sk_C))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_F) = (sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.54  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('70', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('71', plain, (((sk_F) = (sk_C))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['68', '69', '70'])).
% 0.20/0.54  thf('72', plain, (((sk_F) != (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '71'])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['14', '72'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (((X3) = (k1_xboole_0))
% 0.20/0.54          | ((X4) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.54          | ((X4) = (X5)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ sk_D @ sk_E) != (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.54          | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.54          | ((sk_A) = (X1))
% 0.20/0.54          | ((sk_A) = (k1_xboole_0))
% 0.20/0.54          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.54  thf('76', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('77', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ sk_D @ sk_E) != (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.54          | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.54          | ((sk_A) = (X1)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['75', '76', '77'])).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      ((((sk_A) = (sk_D)) | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('eq_res', [status(thm)], ['78'])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (sk_D))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      ((((sk_E) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '45'])).
% 0.20/0.54  thf('84', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (k1_xboole_0))
% 0.20/0.54          | ((sk_A) = (sk_D))
% 0.20/0.54          | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['82', '83'])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('86', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (sk_D))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.54  thf('87', plain,
% 0.20/0.54      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (sk_D))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['86'])).
% 0.20/0.54  thf('88', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (sk_D))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (sk_D))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['89'])).
% 0.20/0.54  thf('91', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('92', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('93', plain, ((((sk_A) = (sk_D)) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['90', '91', '92'])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.54  thf('95', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k3_zfmisc_1 @ sk_D @ X1 @ X0) = (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['93', '94'])).
% 0.20/0.54  thf('96', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (sk_D))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.54  thf('98', plain,
% 0.20/0.54      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['97'])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('100', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (sk_D))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.54  thf('101', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['100'])).
% 0.20/0.54  thf('102', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('103', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('104', plain, (((sk_A) = (sk_D))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['101', '102', '103'])).
% 0.20/0.54  thf('105', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['6', '104'])).
% 0.20/0.54  thf('106', plain,
% 0.20/0.54      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['14', '72'])).
% 0.20/0.54  thf('107', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (((X3) = (k1_xboole_0))
% 0.20/0.54          | ((X4) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.54          | ((X3) = (X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.20/0.54  thf('108', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ sk_D @ sk_E) != (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.54          | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.54          | ((sk_B) = (X0))
% 0.20/0.54          | ((sk_A) = (k1_xboole_0))
% 0.20/0.54          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.54  thf('109', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('110', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('111', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k2_zfmisc_1 @ sk_D @ sk_E) != (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.54          | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.54          | ((sk_B) = (X0)))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['108', '109', '110'])).
% 0.20/0.54  thf('112', plain,
% 0.20/0.54      ((((sk_B) = (sk_E)) | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('eq_res', [status(thm)], ['111'])).
% 0.20/0.54  thf('113', plain,
% 0.20/0.54      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('114', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.20/0.54      inference('split', [status(esa)], ['113'])).
% 0.20/0.54  thf('115', plain, (((sk_F) = (sk_C))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['68', '69', '70'])).
% 0.20/0.54  thf('116', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.20/0.54      inference('split', [status(esa)], ['113'])).
% 0.20/0.54  thf('117', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.54  thf('118', plain, ((((sk_C) = (sk_F)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['117'])).
% 0.20/0.54  thf('119', plain, (((sk_A) = (sk_D))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['101', '102', '103'])).
% 0.20/0.54  thf('120', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.20/0.54      inference('split', [status(esa)], ['113'])).
% 0.20/0.54  thf('121', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['119', '120'])).
% 0.20/0.54  thf('122', plain, ((((sk_A) = (sk_D)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['121'])).
% 0.20/0.54  thf('123', plain,
% 0.20/0.54      (~ (((sk_B) = (sk_E))) | ~ (((sk_A) = (sk_D))) | ~ (((sk_C) = (sk_F)))),
% 0.20/0.54      inference('split', [status(esa)], ['113'])).
% 0.20/0.54  thf('124', plain, (~ (((sk_B) = (sk_E)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['118', '122', '123'])).
% 0.20/0.54  thf('125', plain, (((sk_B) != (sk_E))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['114', '124'])).
% 0.20/0.54  thf('126', plain, (((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['112', '125'])).
% 0.20/0.54  thf('127', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('128', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((sk_D) = (k1_xboole_0))
% 0.20/0.54        | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['126', '127'])).
% 0.20/0.54  thf('129', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['128'])).
% 0.20/0.54  thf('130', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('131', plain, (((sk_A) = (sk_D))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['101', '102', '103'])).
% 0.20/0.54  thf('132', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['130', '131'])).
% 0.20/0.54  thf('133', plain, (((sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.20/0.54  thf('134', plain, (((sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.20/0.54  thf('135', plain,
% 0.20/0.54      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (sk_E))
% 0.20/0.54        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (sk_E)))),
% 0.20/0.54      inference('demod', [status(thm)], ['105', '133', '134'])).
% 0.20/0.54  thf('136', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '45'])).
% 0.20/0.54  thf('137', plain, (((sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.20/0.54  thf('138', plain, (((sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.20/0.54  thf('139', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (sk_E))),
% 0.20/0.54      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.20/0.54  thf('140', plain,
% 0.20/0.54      ((((sk_E) != (sk_E)) | ((k2_zfmisc_1 @ sk_D @ sk_B) = (sk_E)))),
% 0.20/0.54      inference('demod', [status(thm)], ['135', '139'])).
% 0.20/0.54  thf('141', plain, (((k2_zfmisc_1 @ sk_D @ sk_B) = (sk_E))),
% 0.20/0.54      inference('simplify', [status(thm)], ['140'])).
% 0.20/0.54  thf('142', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (k1_xboole_0))
% 0.20/0.54          | ((X1) = (k1_xboole_0))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.54  thf('143', plain, (((sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.20/0.54  thf('144', plain, (((sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.20/0.54  thf('145', plain, (((sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.20/0.54  thf('146', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((X0) = (sk_E))
% 0.20/0.54          | ((X1) = (sk_E))
% 0.20/0.54          | ((k2_zfmisc_1 @ X1 @ X0) != (sk_E)))),
% 0.20/0.54      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 0.20/0.54  thf('147', plain,
% 0.20/0.54      ((((sk_E) != (sk_E)) | ((sk_D) = (sk_E)) | ((sk_B) = (sk_E)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['141', '146'])).
% 0.20/0.54  thf('148', plain, ((((sk_B) = (sk_E)) | ((sk_D) = (sk_E)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['147'])).
% 0.20/0.54  thf('149', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['130', '131'])).
% 0.20/0.54  thf('150', plain, (((sk_E) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.20/0.54  thf('151', plain, (((sk_D) != (sk_E))),
% 0.20/0.54      inference('demod', [status(thm)], ['149', '150'])).
% 0.20/0.54  thf('152', plain, (((sk_B) != (sk_E))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['114', '124'])).
% 0.20/0.54  thf('153', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['148', '151', '152'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
