%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ahw9dmjfkE

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  183 (11938 expanded)
%              Number of leaves         :   15 (3317 expanded)
%              Depth                    :   60
%              Number of atoms          : 1571 (171330 expanded)
%              Number of equality atoms :  385 (41326 expanded)
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

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X3 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('12',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('25',plain,
    ( ( sk_C = sk_F )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C = sk_F )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_F = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_F )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C = sk_F )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_C = sk_F ),
    inference('simplify_reflect-',[status(thm)],['56','57','58'])).

thf('60',plain,(
    sk_F != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','59'])).

thf('61',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['15','60'])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('63',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('74',plain,
    ( ( sk_B = sk_E )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = sk_E )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B = sk_E )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('79',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_B = sk_E ) ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_E )
    | ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_E )
    | ( sk_D = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('94',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_E ) ) ),
    inference('sup+',[status(thm)],['92','97'])).

thf('99',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('103',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_B = sk_E ),
    inference('simplify_reflect-',[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_E )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','107'])).

thf('109',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X3 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('110',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['15','60'])).

thf('111',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X3 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('112',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['112','113','114'])).

thf('116',plain,(
    sk_B = sk_E ),
    inference('simplify_reflect-',[status(thm)],['104','105','106'])).

thf('117',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_D = sk_A )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['109','117'])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    sk_B = sk_E ),
    inference('simplify_reflect-',[status(thm)],['104','105','106'])).

thf('121',plain,(
    sk_E != k1_xboole_0 ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['122'])).

thf('124',plain,(
    sk_C = sk_F ),
    inference('simplify_reflect-',[status(thm)],['56','57','58'])).

thf('125',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['122'])).

thf('126',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    sk_B = sk_E ),
    inference('simplify_reflect-',[status(thm)],['104','105','106'])).

thf('129',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['122'])).

thf('130',plain,
    ( ( sk_E != sk_E )
   <= ( sk_B != sk_E ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    sk_B = sk_E ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['122'])).

thf('133',plain,(
    sk_A != sk_D ),
    inference('sat_resolution*',[status(thm)],['127','131','132'])).

thf('134',plain,(
    sk_A != sk_D ),
    inference(simpl_trail,[status(thm)],['123','133'])).

thf('135',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['118','121','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('137',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    sk_E != k1_xboole_0 ),
    inference(demod,[status(thm)],['119','120'])).

thf('141',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['138','139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('143',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    sk_E != k1_xboole_0 ),
    inference(demod,[status(thm)],['119','120'])).

thf('146',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('147',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('148',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_E )
      = sk_D ) ),
    inference(demod,[status(thm)],['108','146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('150',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('151',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ sk_D @ X1 @ X0 )
      = sk_D ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( sk_D != sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_E )
      = sk_D ) ),
    inference(demod,[status(thm)],['148','152'])).

thf('154',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_E )
    = sk_D ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('156',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('157',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('158',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_D )
      | ( X1 = sk_D )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != sk_D ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,
    ( ( sk_D != sk_D )
    | ( sk_A = sk_D )
    | ( sk_E = sk_D ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,
    ( ( sk_E = sk_D )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    sk_A != sk_D ),
    inference(simpl_trail,[status(thm)],['123','133'])).

thf('163',plain,(
    sk_E != k1_xboole_0 ),
    inference(demod,[status(thm)],['119','120'])).

thf('164',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('165',plain,(
    sk_E != sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['161','162','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ahw9dmjfkE
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 175 iterations in 0.058s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(t36_mcart_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.51     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.51        ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.51          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51            ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51            ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t36_mcart_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d3_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.51       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf(t113_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.51          | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.51  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf(t195_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.51               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (((X3) = (k1_xboole_0))
% 0.20/0.51          | ((k1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X3))
% 0.20/0.51          | ((X4) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.51            = (k2_zfmisc_1 @ X2 @ X1))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.51            = (k2_zfmisc_1 @ X2 @ X1))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.51          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.20/0.51          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (((X3) = (k1_xboole_0))
% 0.20/0.51          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.20/0.51          | ((X4) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)) = (sk_C))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.51  thf('22', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)) = (sk_C))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((((sk_C) = (sk_F))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (sk_F))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (sk_F))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.51  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((sk_C) = (sk_F))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['28', '29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k3_zfmisc_1 @ sk_D @ sk_E @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.20/0.51          | ((sk_F) = (k1_xboole_0))
% 0.20/0.51          | ((sk_C) = (sk_F)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k3_zfmisc_1 @ sk_D @ sk_E @ X0) = (k1_xboole_0))
% 0.20/0.51          | ((sk_C) = (sk_F))
% 0.20/0.51          | ((sk_F) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['33', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (sk_F))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (sk_F))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (sk_F))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (sk_F))
% 0.20/0.51        | ((sk_F) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.51  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain, ((((sk_C) = (sk_F)) | ((sk_F) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['42', '43', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['46', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['45', '49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (sk_F))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ((sk_C) = (sk_F))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.51  thf('57', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('58', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain, (((sk_C) = (sk_F))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['56', '57', '58'])).
% 0.20/0.51  thf('60', plain, (((sk_F) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '59'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['15', '60'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (((X3) = (k1_xboole_0))
% 0.20/0.51          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.20/0.51          | ((X4) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['61', '62'])).
% 0.20/0.51  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('65', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['63', '64', '65'])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0))
% 0.20/0.52        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.52  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('71', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['69', '70', '71'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (((X3) = (k1_xboole_0))
% 0.20/0.52          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.20/0.52          | ((X4) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((((sk_B) = (sk_E))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (sk_E))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      ((((sk_B) = (sk_E)) | ((sk_E) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.20/0.52           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.52  thf('83', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (k1_xboole_0))
% 0.20/0.52          | ((sk_D) = (k1_xboole_0))
% 0.20/0.52          | ((sk_B) = (sk_E)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['77', '82'])).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (sk_E))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (sk_E)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (sk_E))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (sk_E)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['88'])).
% 0.20/0.52  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('92', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_B) = (sk_E)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['89', '90', '91'])).
% 0.20/0.52  thf('93', plain,
% 0.20/0.52      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.20/0.52           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['93', '94'])).
% 0.20/0.52  thf('96', plain,
% 0.20/0.52      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.52  thf('98', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k3_zfmisc_1 @ sk_D @ X1 @ X0) = (k1_xboole_0)) | ((sk_B) = (sk_E)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['92', '97'])).
% 0.20/0.52  thf('99', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('100', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (sk_E))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.52  thf('101', plain,
% 0.20/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_B) = (sk_E)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['100'])).
% 0.20/0.52  thf('102', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('103', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (sk_E))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.52  thf('104', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_E)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['103'])).
% 0.20/0.52  thf('105', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('106', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('107', plain, (((sk_B) = (sk_E))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['104', '105', '106'])).
% 0.20/0.52  thf('108', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '107'])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (((X3) = (k1_xboole_0))
% 0.20/0.52          | ((k1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X3))
% 0.20/0.52          | ((X4) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['15', '60'])).
% 0.20/0.52  thf('111', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (((X3) = (k1_xboole_0))
% 0.20/0.52          | ((k1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X3))
% 0.20/0.52          | ((X4) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.52  thf('112', plain,
% 0.20/0.52      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['110', '111'])).
% 0.20/0.52  thf('113', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('114', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('115', plain,
% 0.20/0.52      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['112', '113', '114'])).
% 0.20/0.52  thf('116', plain, (((sk_B) = (sk_E))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['104', '105', '106'])).
% 0.20/0.52  thf('117', plain,
% 0.20/0.52      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['115', '116'])).
% 0.20/0.52  thf('118', plain,
% 0.20/0.52      ((((sk_D) = (sk_A))
% 0.20/0.52        | ((sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['109', '117'])).
% 0.20/0.52  thf('119', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('120', plain, (((sk_B) = (sk_E))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['104', '105', '106'])).
% 0.20/0.52  thf('121', plain, (((sk_E) != (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['119', '120'])).
% 0.20/0.52  thf('122', plain,
% 0.20/0.52      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('123', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.20/0.52      inference('split', [status(esa)], ['122'])).
% 0.20/0.52  thf('124', plain, (((sk_C) = (sk_F))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['56', '57', '58'])).
% 0.20/0.52  thf('125', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.20/0.52      inference('split', [status(esa)], ['122'])).
% 0.20/0.52  thf('126', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['124', '125'])).
% 0.20/0.52  thf('127', plain, ((((sk_C) = (sk_F)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['126'])).
% 0.20/0.52  thf('128', plain, (((sk_B) = (sk_E))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['104', '105', '106'])).
% 0.20/0.52  thf('129', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.20/0.52      inference('split', [status(esa)], ['122'])).
% 0.20/0.52  thf('130', plain, ((((sk_E) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['128', '129'])).
% 0.20/0.52  thf('131', plain, ((((sk_B) = (sk_E)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['130'])).
% 0.20/0.52  thf('132', plain,
% 0.20/0.52      (~ (((sk_A) = (sk_D))) | ~ (((sk_B) = (sk_E))) | ~ (((sk_C) = (sk_F)))),
% 0.20/0.52      inference('split', [status(esa)], ['122'])).
% 0.20/0.52  thf('133', plain, (~ (((sk_A) = (sk_D)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['127', '131', '132'])).
% 0.20/0.52  thf('134', plain, (((sk_A) != (sk_D))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['123', '133'])).
% 0.20/0.52  thf('135', plain,
% 0.20/0.52      ((((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['118', '121', '134'])).
% 0.20/0.52  thf('136', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('137', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0))
% 0.20/0.52        | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['135', '136'])).
% 0.20/0.52  thf('138', plain,
% 0.20/0.52      ((((sk_E) = (k1_xboole_0))
% 0.20/0.52        | ((sk_A) = (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['137'])).
% 0.20/0.52  thf('139', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('140', plain, (((sk_E) != (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['119', '120'])).
% 0.20/0.52  thf('141', plain,
% 0.20/0.52      ((((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['138', '139', '140'])).
% 0.20/0.52  thf('142', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('143', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((sk_D) = (k1_xboole_0))
% 0.20/0.52        | ((sk_E) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['141', '142'])).
% 0.20/0.52  thf('144', plain, ((((sk_E) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['143'])).
% 0.20/0.52  thf('145', plain, (((sk_E) != (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['119', '120'])).
% 0.20/0.52  thf('146', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('147', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('148', plain,
% 0.20/0.52      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (sk_D))
% 0.20/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_E) = (sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['108', '146', '147'])).
% 0.20/0.52  thf('149', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.52  thf('150', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('151', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('152', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ sk_D @ X1 @ X0) = (sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.20/0.52  thf('153', plain,
% 0.20/0.52      ((((sk_D) != (sk_D)) | ((k2_zfmisc_1 @ sk_A @ sk_E) = (sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['148', '152'])).
% 0.20/0.52  thf('154', plain, (((k2_zfmisc_1 @ sk_A @ sk_E) = (sk_D))),
% 0.20/0.52      inference('simplify', [status(thm)], ['153'])).
% 0.20/0.52  thf('155', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (k1_xboole_0))
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('156', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('157', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('158', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('159', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X0) = (sk_D))
% 0.20/0.52          | ((X1) = (sk_D))
% 0.20/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 0.20/0.52  thf('160', plain,
% 0.20/0.52      ((((sk_D) != (sk_D)) | ((sk_A) = (sk_D)) | ((sk_E) = (sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['154', '159'])).
% 0.20/0.52  thf('161', plain, ((((sk_E) = (sk_D)) | ((sk_A) = (sk_D)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['160'])).
% 0.20/0.52  thf('162', plain, (((sk_A) != (sk_D))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['123', '133'])).
% 0.20/0.52  thf('163', plain, (((sk_E) != (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['119', '120'])).
% 0.20/0.52  thf('164', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.52  thf('165', plain, (((sk_E) != (sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['163', '164'])).
% 0.20/0.52  thf('166', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['161', '162', '165'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
