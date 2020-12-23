%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0876+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L1n9L9ZmcB

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:38 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  140 (4580 expanded)
%              Number of leaves         :   13 (1249 expanded)
%              Depth                    :   44
%              Number of atoms          : 1162 (65251 expanded)
%              Number of equality atoms :  276 (15569 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X7 @ X6 )
       != ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( X7 = X8 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('17',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X7 @ X6 )
       != ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( X6 = X9 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_F = sk_C )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_F = sk_C ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_F = sk_C ) ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf('43',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = sk_C )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = sk_C ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_F = sk_C ),
    inference('simplify_reflect-',[status(thm)],['48','49','50'])).

thf('52',plain,(
    sk_F != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','51'])).

thf('53',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','52'])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X7 @ X6 )
       != ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_A = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_A = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( sk_A = sk_D )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_A = sk_D ),
    inference('simplify_reflect-',[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','72'])).

thf('74',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','52'])).

thf('75',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X7 @ X6 )
       != ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( X6 = X9 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_B = X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( sk_B = sk_E )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['79'])).

thf('81',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,(
    sk_F = sk_C ),
    inference('simplify_reflect-',[status(thm)],['48','49','50'])).

thf('84',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['81'])).

thf('85',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    sk_A = sk_D ),
    inference('simplify_reflect-',[status(thm)],['69','70','71'])).

thf('88',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['81'])).

thf('89',plain,
    ( ( sk_D != sk_D )
   <= ( sk_A != sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( sk_B != sk_E )
    | ( sk_A != sk_D )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['81'])).

thf('92',plain,(
    sk_B != sk_E ),
    inference('sat_resolution*',[status(thm)],['86','90','91'])).

thf('93',plain,(
    sk_B != sk_E ),
    inference(simpl_trail,[status(thm)],['82','92'])).

thf('94',plain,
    ( ( k2_zfmisc_1 @ sk_D @ sk_E )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['80','93'])).

thf('95',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_A = sk_D ),
    inference('simplify_reflect-',[status(thm)],['69','70','71'])).

thf('100',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

thf('102',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

thf('103',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != sk_E )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = sk_E ) ),
    inference(demod,[status(thm)],['73','101','102'])).

thf('104',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

thf('110',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
      = sk_E ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = sk_E ) ),
    inference(demod,[status(thm)],['103','111'])).

thf('113',plain,
    ( ( k2_zfmisc_1 @ sk_D @ sk_B )
    = sk_E ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('115',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

thf('116',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

thf('117',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

thf('118',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = sk_E )
      | ( X4 = sk_E )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != sk_E ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,
    ( ( sk_E != sk_E )
    | ( sk_D = sk_E )
    | ( sk_B = sk_E ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,
    ( ( sk_B = sk_E )
    | ( sk_D = sk_E ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('122',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['97','100'])).

thf('123',plain,(
    sk_D != sk_E ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    sk_B != sk_E ),
    inference(simpl_trail,[status(thm)],['82','92'])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['120','123','124'])).


%------------------------------------------------------------------------------
