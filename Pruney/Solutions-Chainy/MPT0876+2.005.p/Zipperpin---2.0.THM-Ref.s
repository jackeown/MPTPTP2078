%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tE1ETe559q

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:20 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  154 (3769 expanded)
%              Number of leaves         :   16 (1067 expanded)
%              Depth                    :   52
%              Number of atoms          : 1358 (56602 expanded)
%              Number of equality atoms :  331 (13841 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('2',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('9',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('17',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_D @ sk_E ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('27',plain,
    ( ( sk_C = sk_F )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('29',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('31',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( k1_xboole_0 = sk_B ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C = sk_F )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_F = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( X5 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X6 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('39',plain,(
    ! [X6: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X6 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = X0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference(demod,[status(thm)],['37','45'])).

thf('47',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( X8 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X6 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['49','51'])).

thf('53',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    sk_F != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','55'])).

thf('57',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_D @ sk_E ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('59',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('64',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_D @ sk_E ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','56'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('66',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('71',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('73',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( k1_xboole_0 = sk_B ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('79',plain,
    ( ( sk_A = sk_D )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('81',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_E )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_A = sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_E ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( k1_xboole_0 = sk_E )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference('sup+',[status(thm)],['63','82'])).

thf('84',plain,
    ( ( sk_A = sk_D )
    | ( sk_D = k1_xboole_0 )
    | ( k1_xboole_0 = sk_E ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( X6 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X6 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('86',plain,(
    ! [X5: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X5 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['84','86'])).

thf('88',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X6: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X6 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('94',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','95'])).

thf('97',plain,
    ( ( sk_E = sk_B )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','96'])).

thf('98',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('100',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['54'])).

thf('104',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['101'])).

thf('105',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('108',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['101'])).

thf('109',plain,
    ( ( sk_D != sk_D )
   <= ( sk_A != sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( sk_B != sk_E )
    | ( sk_A != sk_D )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['101'])).

thf('112',plain,(
    sk_B != sk_E ),
    inference('sat_resolution*',[status(thm)],['106','110','111'])).

thf('113',plain,(
    sk_B != sk_E ),
    inference(simpl_trail,[status(thm)],['102','112'])).

thf('114',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['97','100','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('116',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('118',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( k1_xboole_0 = sk_B ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('122',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('124',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_E )
    | ( sk_E = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_E ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('127',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k1_xboole_0 = sk_E )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','127'])).

thf('129',plain,(
    k1_xboole_0 = sk_E ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != sk_E ),
    inference(demod,[status(thm)],['6','129'])).

thf('131',plain,(
    ! [X5: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X5 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('132',plain,(
    k1_xboole_0 = sk_E ),
    inference(simplify,[status(thm)],['128'])).

thf('133',plain,(
    k1_xboole_0 = sk_E ),
    inference(simplify,[status(thm)],['128'])).

thf('134',plain,(
    ! [X5: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X5 @ sk_E @ X8 )
      = sk_E ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['130','134'])).

thf('136',plain,(
    $false ),
    inference(simplify,[status(thm)],['135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tE1ETe559q
% 0.15/0.37  % Computer   : n004.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:14:09 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 663 iterations in 0.154s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.63  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.44/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(t36_mcart_1, conjecture,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.63     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.44/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.63         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.44/0.63         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.63        ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.44/0.63          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.63            ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.44/0.63            ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t36_mcart_1])).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t35_mcart_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.44/0.63         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.44/0.63       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.63         (((k3_zfmisc_1 @ X5 @ X6 @ X7) != (k1_xboole_0))
% 0.44/0.63          | ((X7) = (k1_xboole_0))
% 0.44/0.63          | ((X6) = (k1_xboole_0))
% 0.44/0.63          | ((X5) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.63  thf('3', plain, (((sk_C) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('6', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.44/0.63  thf(t60_relat_1, axiom,
% 0.44/0.63    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.44/0.63     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.63  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.63  thf(t195_relat_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.44/0.63          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.44/0.63               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.44/0.63  thf('8', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(d3_zfmisc_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.44/0.63       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.44/0.63  thf('10', plain,
% 0.44/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.63         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 0.44/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 0.44/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.44/0.63  thf('11', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X0))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('12', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.44/0.63            = (k2_zfmisc_1 @ X2 @ X1))
% 0.44/0.63          | ((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.63          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['9', '12'])).
% 0.44/0.63  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('15', plain,
% 0.44/0.63      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.63          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.44/0.63  thf('16', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.44/0.63            = (k2_zfmisc_1 @ X2 @ X1))
% 0.44/0.63          | ((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.63  thf('17', plain,
% 0.44/0.63      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_D @ sk_E))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_F) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['15', '16'])).
% 0.44/0.63  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.63         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 0.44/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 0.44/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('22', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.44/0.63          | ((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.44/0.63  thf('23', plain,
% 0.44/0.63      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)) = (sk_C))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['19', '22'])).
% 0.44/0.63  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('25', plain,
% 0.44/0.63      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)) = (sk_C))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.44/0.63  thf('26', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.44/0.63          | ((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      ((((sk_C) = (sk_F))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_F) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('29', plain,
% 0.44/0.63      ((((k2_relat_1 @ k1_xboole_0) = (sk_B))
% 0.44/0.63        | ((sk_F) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_C) = (sk_F))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.44/0.63  thf('30', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.63  thf('31', plain,
% 0.44/0.63      ((((k1_xboole_0) = (sk_B))
% 0.44/0.63        | ((sk_F) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_C) = (sk_F))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.44/0.63  thf('32', plain,
% 0.44/0.63      ((((sk_A) = (k1_xboole_0))
% 0.44/0.63        | ((sk_C) = (sk_F))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_F) = (k1_xboole_0))
% 0.44/0.63        | ((k1_xboole_0) = (sk_B)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.44/0.63  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('35', plain,
% 0.44/0.63      ((((sk_C) = (sk_F))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_F) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['32', '33', '34'])).
% 0.44/0.63  thf('36', plain,
% 0.44/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.63         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 0.44/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 0.44/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.44/0.63  thf('37', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((k3_zfmisc_1 @ sk_D @ sk_E @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.44/0.63          | ((sk_F) = (k1_xboole_0))
% 0.44/0.63          | ((sk_C) = (sk_F)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['35', '36'])).
% 0.44/0.63  thf('38', plain,
% 0.44/0.63      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.44/0.63         (((X5) != (k1_xboole_0))
% 0.44/0.63          | ((k3_zfmisc_1 @ X5 @ X6 @ X8) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.44/0.63  thf('39', plain,
% 0.44/0.63      (![X6 : $i, X8 : $i]:
% 0.44/0.63         ((k3_zfmisc_1 @ k1_xboole_0 @ X6 @ X8) = (k1_xboole_0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['38'])).
% 0.44/0.63  thf('40', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.44/0.63          | ((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.44/0.63  thf('41', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k2_relat_1 @ k1_xboole_0) = (X0))
% 0.44/0.63          | ((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.44/0.63          | ((X0) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['39', '40'])).
% 0.44/0.63  thf('42', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.63  thf('43', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k1_xboole_0) = (X0))
% 0.44/0.63          | ((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.44/0.63          | ((X0) = (k1_xboole_0)))),
% 0.44/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.44/0.63          | ((k1_xboole_0) = (X0)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['43'])).
% 0.44/0.63  thf('45', plain,
% 0.44/0.63      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('condensation', [status(thm)], ['44'])).
% 0.44/0.63  thf('46', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((k3_zfmisc_1 @ sk_D @ sk_E @ X0) = (k1_xboole_0))
% 0.44/0.63          | ((sk_F) = (k1_xboole_0))
% 0.44/0.63          | ((sk_C) = (sk_F)))),
% 0.44/0.63      inference('demod', [status(thm)], ['37', '45'])).
% 0.44/0.63  thf('47', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.44/0.63  thf('48', plain,
% 0.44/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.63        | ((sk_C) = (sk_F))
% 0.44/0.63        | ((sk_F) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.44/0.63  thf('49', plain, ((((sk_F) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['48'])).
% 0.44/0.63  thf('50', plain,
% 0.44/0.63      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.44/0.63         (((X8) != (k1_xboole_0))
% 0.44/0.63          | ((k3_zfmisc_1 @ X5 @ X6 @ X8) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.44/0.63  thf('51', plain,
% 0.44/0.63      (![X5 : $i, X6 : $i]:
% 0.44/0.63         ((k3_zfmisc_1 @ X5 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['50'])).
% 0.44/0.63  thf('52', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['49', '51'])).
% 0.44/0.63  thf('53', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.44/0.63  thf('54', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.44/0.63  thf('55', plain, (((sk_C) = (sk_F))),
% 0.44/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.44/0.63  thf('56', plain, (((sk_F) != (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['18', '55'])).
% 0.44/0.63  thf('57', plain,
% 0.44/0.63      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_D @ sk_E))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['17', '56'])).
% 0.44/0.63  thf('58', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('59', plain,
% 0.44/0.63      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['57', '58'])).
% 0.44/0.63  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('62', plain,
% 0.44/0.63      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['59', '60', '61'])).
% 0.44/0.63  thf('63', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.63  thf('64', plain,
% 0.44/0.63      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_D @ sk_E))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['17', '56'])).
% 0.44/0.63  thf('65', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X0))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('66', plain,
% 0.44/0.63      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['64', '65'])).
% 0.44/0.63  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('68', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('69', plain,
% 0.44/0.63      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['66', '67', '68'])).
% 0.44/0.63  thf('70', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('71', plain,
% 0.44/0.63      ((((k2_relat_1 @ k1_xboole_0) = (sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['69', '70'])).
% 0.44/0.63  thf('72', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.63  thf('73', plain,
% 0.44/0.63      ((((k1_xboole_0) = (sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.63      inference('demod', [status(thm)], ['71', '72'])).
% 0.44/0.63  thf('74', plain,
% 0.44/0.63      ((((sk_A) = (k1_xboole_0))
% 0.44/0.63        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k1_xboole_0) = (sk_B)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['73'])).
% 0.44/0.63  thf('75', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('76', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('77', plain,
% 0.44/0.63      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['74', '75', '76'])).
% 0.44/0.63  thf('78', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X0))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('79', plain,
% 0.44/0.63      ((((sk_A) = (sk_D))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['77', '78'])).
% 0.44/0.63  thf('80', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('81', plain,
% 0.44/0.63      ((((k2_relat_1 @ k1_xboole_0) = (sk_E))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (sk_D))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['79', '80'])).
% 0.44/0.63  thf('82', plain,
% 0.44/0.63      ((((sk_A) = (sk_D))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0))
% 0.44/0.63        | ((k2_relat_1 @ k1_xboole_0) = (sk_E)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['81'])).
% 0.44/0.63  thf('83', plain,
% 0.44/0.63      ((((k1_xboole_0) = (sk_E))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (sk_D)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['63', '82'])).
% 0.44/0.63  thf('84', plain,
% 0.44/0.63      ((((sk_A) = (sk_D)) | ((sk_D) = (k1_xboole_0)) | ((k1_xboole_0) = (sk_E)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['83'])).
% 0.44/0.63  thf('85', plain,
% 0.44/0.63      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.44/0.63         (((X6) != (k1_xboole_0))
% 0.44/0.63          | ((k3_zfmisc_1 @ X5 @ X6 @ X8) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.44/0.63  thf('86', plain,
% 0.44/0.63      (![X5 : $i, X8 : $i]:
% 0.44/0.63         ((k3_zfmisc_1 @ X5 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['85'])).
% 0.44/0.63  thf('87', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (k1_xboole_0))
% 0.44/0.63          | ((sk_D) = (k1_xboole_0))
% 0.44/0.63          | ((sk_A) = (sk_D)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['84', '86'])).
% 0.44/0.63  thf('88', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.44/0.63  thf('89', plain,
% 0.44/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (sk_D))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['87', '88'])).
% 0.44/0.63  thf('90', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['89'])).
% 0.44/0.63  thf('91', plain,
% 0.44/0.63      (![X6 : $i, X8 : $i]:
% 0.44/0.63         ((k3_zfmisc_1 @ k1_xboole_0 @ X6 @ X8) = (k1_xboole_0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['38'])).
% 0.44/0.63  thf('92', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k3_zfmisc_1 @ sk_D @ X1 @ X0) = (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['90', '91'])).
% 0.44/0.63  thf('93', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.44/0.63  thf('94', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['92', '93'])).
% 0.44/0.63  thf('95', plain, (((sk_A) = (sk_D))),
% 0.44/0.63      inference('simplify', [status(thm)], ['94'])).
% 0.44/0.63  thf('96', plain,
% 0.44/0.63      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 0.44/0.63      inference('demod', [status(thm)], ['62', '95'])).
% 0.44/0.63  thf('97', plain,
% 0.44/0.63      ((((sk_E) = (sk_B))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['8', '96'])).
% 0.44/0.63  thf('98', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('99', plain, (((sk_A) = (sk_D))),
% 0.44/0.63      inference('simplify', [status(thm)], ['94'])).
% 0.44/0.63  thf('100', plain, (((sk_D) != (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['98', '99'])).
% 0.44/0.63  thf('101', plain,
% 0.44/0.63      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('102', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.44/0.63      inference('split', [status(esa)], ['101'])).
% 0.44/0.63  thf('103', plain, (((sk_C) = (sk_F))),
% 0.44/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.44/0.63  thf('104', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.44/0.63      inference('split', [status(esa)], ['101'])).
% 0.44/0.63  thf('105', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['103', '104'])).
% 0.44/0.63  thf('106', plain, ((((sk_C) = (sk_F)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['105'])).
% 0.44/0.63  thf('107', plain, (((sk_A) = (sk_D))),
% 0.44/0.63      inference('simplify', [status(thm)], ['94'])).
% 0.44/0.63  thf('108', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.44/0.63      inference('split', [status(esa)], ['101'])).
% 0.44/0.63  thf('109', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['107', '108'])).
% 0.44/0.63  thf('110', plain, ((((sk_A) = (sk_D)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['109'])).
% 0.44/0.63  thf('111', plain,
% 0.44/0.63      (~ (((sk_B) = (sk_E))) | ~ (((sk_A) = (sk_D))) | ~ (((sk_C) = (sk_F)))),
% 0.44/0.63      inference('split', [status(esa)], ['101'])).
% 0.44/0.63  thf('112', plain, (~ (((sk_B) = (sk_E)))),
% 0.44/0.63      inference('sat_resolution*', [status(thm)], ['106', '110', '111'])).
% 0.44/0.63  thf('113', plain, (((sk_B) != (sk_E))),
% 0.44/0.63      inference('simpl_trail', [status(thm)], ['102', '112'])).
% 0.44/0.63  thf('114', plain,
% 0.44/0.63      ((((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['97', '100', '113'])).
% 0.44/0.63  thf('115', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('116', plain,
% 0.44/0.63      ((((k2_relat_1 @ k1_xboole_0) = (sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['114', '115'])).
% 0.44/0.63  thf('117', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.63  thf('118', plain,
% 0.44/0.63      ((((k1_xboole_0) = (sk_B))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0)))),
% 0.44/0.63      inference('demod', [status(thm)], ['116', '117'])).
% 0.44/0.63  thf('119', plain,
% 0.44/0.63      ((((sk_D) = (k1_xboole_0))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k1_xboole_0) = (sk_B)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['118'])).
% 0.44/0.63  thf('120', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('121', plain, (((sk_D) != (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['98', '99'])).
% 0.44/0.63  thf('122', plain,
% 0.44/0.63      ((((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['119', '120', '121'])).
% 0.44/0.63  thf('123', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((X0) = (k1_xboole_0))
% 0.44/0.63          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.44/0.63          | ((X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.44/0.63  thf('124', plain,
% 0.44/0.63      ((((k2_relat_1 @ k1_xboole_0) = (sk_E))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((sk_D) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['122', '123'])).
% 0.44/0.63  thf('125', plain,
% 0.44/0.63      ((((sk_D) = (k1_xboole_0))
% 0.44/0.63        | ((sk_E) = (k1_xboole_0))
% 0.44/0.63        | ((k2_relat_1 @ k1_xboole_0) = (sk_E)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['124'])).
% 0.44/0.63  thf('126', plain, (((sk_D) != (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['98', '99'])).
% 0.44/0.63  thf('127', plain,
% 0.44/0.63      ((((sk_E) = (k1_xboole_0)) | ((k2_relat_1 @ k1_xboole_0) = (sk_E)))),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['125', '126'])).
% 0.44/0.63  thf('128', plain, ((((k1_xboole_0) = (sk_E)) | ((sk_E) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['7', '127'])).
% 0.44/0.63  thf('129', plain, (((k1_xboole_0) = (sk_E))),
% 0.44/0.63      inference('simplify', [status(thm)], ['128'])).
% 0.44/0.63  thf('130', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (sk_E))),
% 0.44/0.63      inference('demod', [status(thm)], ['6', '129'])).
% 0.44/0.63  thf('131', plain,
% 0.44/0.63      (![X5 : $i, X8 : $i]:
% 0.44/0.63         ((k3_zfmisc_1 @ X5 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['85'])).
% 0.44/0.63  thf('132', plain, (((k1_xboole_0) = (sk_E))),
% 0.44/0.63      inference('simplify', [status(thm)], ['128'])).
% 0.44/0.63  thf('133', plain, (((k1_xboole_0) = (sk_E))),
% 0.44/0.63      inference('simplify', [status(thm)], ['128'])).
% 0.44/0.63  thf('134', plain,
% 0.44/0.63      (![X5 : $i, X8 : $i]: ((k3_zfmisc_1 @ X5 @ sk_E @ X8) = (sk_E))),
% 0.44/0.63      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.44/0.63  thf('135', plain, (((sk_E) != (sk_E))),
% 0.44/0.63      inference('demod', [status(thm)], ['130', '134'])).
% 0.44/0.63  thf('136', plain, ($false), inference('simplify', [status(thm)], ['135'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
