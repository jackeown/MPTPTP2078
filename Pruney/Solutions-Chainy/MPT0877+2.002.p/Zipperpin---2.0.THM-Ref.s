%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.okg1jqZmXD

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  173 (10619 expanded)
%              Number of leaves         :   15 (2803 expanded)
%              Depth                    :   67
%              Number of atoms          : 1761 (140273 expanded)
%              Number of equality atoms :  423 (29532 expanded)
%              Maximal formula depth    :   14 (   6 average)

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

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

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
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('12',plain,
    ( ( sk_C = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_F = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
        = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference(demod,[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','17'])).

thf('19',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('20',plain,
    ( ( sk_C = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_C = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_C )
        = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_C = sk_F )
      | ( sk_D = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','28'])).

thf('30',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('31',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_F = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_C = sk_F )
      | ( sk_D = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_C = sk_F )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_F )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','54'])).

thf('56',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','54'])).

thf('57',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','54'])).

thf('58',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','54'])).

thf('59',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X3 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('64',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['53'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X3 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('70',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_A )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X3 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('75',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','80'])).

thf('82',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('83',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','85'])).

thf('87',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('88',plain,
    ( ( sk_A = sk_D )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','90'])).

thf('92',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('93',plain,
    ( ( sk_A = sk_D )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('97',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_D ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( k3_zfmisc_1 @ sk_D @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['55','103'])).

thf('105',plain,
    ( ( k3_zfmisc_1 @ sk_D @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['55','103'])).

thf('106',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('107',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('108',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('109',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['102'])).

thf('111',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['102'])).

thf('112',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( sk_E = sk_B )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('114',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_E = sk_B ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['53'])).

thf('118',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['115'])).

thf('119',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['102'])).

thf('122',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['115'])).

thf('123',plain,
    ( ( sk_D != sk_D )
   <= ( sk_A != sk_D ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    sk_A = sk_D ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( sk_B != sk_E )
    | ( sk_A != sk_D )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['115'])).

thf('126',plain,(
    sk_B != sk_E ),
    inference('sat_resolution*',[status(thm)],['120','124','125'])).

thf('127',plain,(
    sk_B != sk_E ),
    inference(simpl_trail,[status(thm)],['116','126'])).

thf('128',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['114','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('130',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_E )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('133',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','136'])).

thf('138',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('139',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','141'])).

thf('143',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('144',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_E @ X0 )
        = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('148',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != sk_D ),
    inference(demod,[status(thm)],['2','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('152',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['148'])).

thf('153',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['148'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ sk_D @ X1 @ X0 )
      = sk_D ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    sk_D != sk_D ),
    inference(demod,[status(thm)],['150','154'])).

thf('156',plain,(
    $false ),
    inference(simplify,[status(thm)],['155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.okg1jqZmXD
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:53:51 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 273 iterations in 0.117s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(t37_mcart_1, conjecture,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.58     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.58       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.58         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.58        ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.58          ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.58            ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t37_mcart_1])).
% 0.21/0.58  thf('0', plain, (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) != (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('2', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(d3_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.58       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.58         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.21/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.58  thf(t195_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.58          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.21/0.58               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X3 : $i, X4 : $i]:
% 0.21/0.58         (((X3) = (k1_xboole_0))
% 0.21/0.58          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.21/0.58          | ((X4) = (k1_xboole_0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.21/0.58          | ((X0) = (k1_xboole_0))
% 0.21/0.58          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)) = (sk_C))
% 0.21/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.58        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.21/0.58          | ((X0) = (k1_xboole_0))
% 0.21/0.58          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      ((((sk_C) = (sk_F))
% 0.21/0.58        | ((sk_C) = (k1_xboole_0))
% 0.21/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.42/0.58  thf('13', plain,
% 0.42/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.42/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.42/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.58  thf('14', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.42/0.58          | ((sk_F) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58          | ((sk_C) = (k1_xboole_0))
% 0.42/0.58          | ((sk_C) = (sk_F)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.42/0.58  thf(t113_zfmisc_1, axiom,
% 0.42/0.58    (![A:$i,B:$i]:
% 0.42/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.58  thf('15', plain,
% 0.42/0.58      (![X1 : $i, X2 : $i]:
% 0.42/0.58         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.58  thf('16', plain,
% 0.42/0.58      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.58  thf('17', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ sk_A @ sk_B @ X0) = (k1_xboole_0))
% 0.42/0.58          | ((sk_F) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58          | ((sk_C) = (k1_xboole_0))
% 0.42/0.58          | ((sk_C) = (sk_F)))),
% 0.42/0.58      inference('demod', [status(thm)], ['14', '16'])).
% 0.42/0.58  thf('18', plain,
% 0.42/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (sk_F))
% 0.42/0.58        | ((sk_C) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['5', '17'])).
% 0.42/0.58  thf('19', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('20', plain,
% 0.42/0.58      ((((sk_C) = (sk_F))
% 0.42/0.58        | ((sk_C) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.42/0.58  thf('21', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((X0) = (k1_xboole_0))
% 0.42/0.58          | ((X1) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.58  thf('22', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (sk_F))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.58  thf('23', plain,
% 0.42/0.58      ((((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (sk_F))
% 0.42/0.58        | ((sk_C) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.42/0.58  thf('24', plain,
% 0.42/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.42/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.42/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.58  thf('25', plain,
% 0.42/0.58      (![X1 : $i, X2 : $i]:
% 0.42/0.58         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.58  thf('26', plain,
% 0.42/0.58      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.42/0.58  thf('27', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.58      inference('sup+', [status(thm)], ['24', '26'])).
% 0.42/0.58  thf('28', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ X0 @ sk_C) = (k1_xboole_0))
% 0.42/0.58          | ((sk_F) = (k1_xboole_0))
% 0.42/0.58          | ((sk_C) = (sk_F))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0))
% 0.42/0.58          | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['23', '27'])).
% 0.42/0.58  thf('29', plain,
% 0.42/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (sk_F))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['4', '28'])).
% 0.42/0.58  thf('30', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('31', plain,
% 0.42/0.58      ((((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (sk_F))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.42/0.58  thf('32', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.58      inference('sup+', [status(thm)], ['24', '26'])).
% 0.42/0.58  thf('33', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0))
% 0.42/0.58          | ((sk_C) = (sk_F))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0))
% 0.42/0.58          | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['31', '32'])).
% 0.42/0.58  thf('34', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('35', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (sk_F)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.58  thf('36', plain,
% 0.42/0.58      ((((sk_C) = (sk_F)) | ((sk_D) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.42/0.58  thf('37', plain,
% 0.42/0.58      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.42/0.58  thf('38', plain,
% 0.42/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.42/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.42/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.58  thf('39', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.42/0.58           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.42/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.42/0.58  thf('40', plain,
% 0.42/0.58      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.58  thf('41', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.58  thf('42', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (k1_xboole_0))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0))
% 0.42/0.58          | ((sk_C) = (sk_F)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['36', '41'])).
% 0.42/0.58  thf('43', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('44', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (sk_F))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.58  thf('45', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['44'])).
% 0.42/0.58  thf('46', plain,
% 0.42/0.58      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.58  thf('47', plain,
% 0.42/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.42/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.42/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.58  thf('48', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.42/0.58           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.42/0.58      inference('sup+', [status(thm)], ['46', '47'])).
% 0.42/0.58  thf('49', plain,
% 0.42/0.58      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.58  thf('50', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.58  thf('51', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ sk_D @ X1 @ X0) = (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['45', '50'])).
% 0.42/0.58  thf('52', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('53', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (sk_F)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.58  thf('54', plain, (((sk_C) = (sk_F))),
% 0.42/0.58      inference('simplify', [status(thm)], ['53'])).
% 0.42/0.58  thf('55', plain,
% 0.42/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.58      inference('demod', [status(thm)], ['3', '54'])).
% 0.42/0.58  thf('56', plain,
% 0.42/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.58      inference('demod', [status(thm)], ['3', '54'])).
% 0.42/0.58  thf('57', plain,
% 0.42/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.58      inference('demod', [status(thm)], ['3', '54'])).
% 0.42/0.58  thf('58', plain,
% 0.42/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.58      inference('demod', [status(thm)], ['3', '54'])).
% 0.42/0.58  thf('59', plain,
% 0.42/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.42/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.42/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.58  thf('60', plain,
% 0.42/0.58      (![X3 : $i, X4 : $i]:
% 0.42/0.58         (((X3) = (k1_xboole_0))
% 0.42/0.58          | ((k1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X3))
% 0.42/0.58          | ((X4) = (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.42/0.58  thf('61', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.58         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.42/0.58            = (k2_zfmisc_1 @ X2 @ X1))
% 0.42/0.58          | ((X0) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['59', '60'])).
% 0.42/0.58  thf('62', plain,
% 0.42/0.58      (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('63', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.58         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.42/0.58            = (k2_zfmisc_1 @ X2 @ X1))
% 0.42/0.58          | ((X0) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['59', '60'])).
% 0.42/0.58  thf('64', plain,
% 0.42/0.58      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.42/0.58          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_C) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['62', '63'])).
% 0.42/0.58  thf('65', plain, (((sk_C) = (sk_F))),
% 0.42/0.58      inference('simplify', [status(thm)], ['53'])).
% 0.42/0.58  thf('66', plain,
% 0.42/0.58      ((((k1_relat_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))
% 0.42/0.58          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0)))),
% 0.42/0.58      inference('demod', [status(thm)], ['64', '65'])).
% 0.42/0.58  thf('67', plain,
% 0.42/0.58      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['61', '66'])).
% 0.42/0.58  thf('68', plain,
% 0.42/0.58      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['67'])).
% 0.42/0.58  thf('69', plain,
% 0.42/0.58      (![X3 : $i, X4 : $i]:
% 0.42/0.58         (((X3) = (k1_xboole_0))
% 0.42/0.58          | ((k1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X3))
% 0.42/0.58          | ((X4) = (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.42/0.58  thf('70', plain,
% 0.42/0.58      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['68', '69'])).
% 0.42/0.58  thf('71', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((X0) = (k1_xboole_0))
% 0.42/0.58          | ((X1) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.58  thf('72', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.58  thf('73', plain,
% 0.42/0.58      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_A))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['72'])).
% 0.42/0.58  thf('74', plain,
% 0.42/0.58      (![X3 : $i, X4 : $i]:
% 0.42/0.58         (((X3) = (k1_xboole_0))
% 0.42/0.58          | ((k1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X3))
% 0.42/0.58          | ((X4) = (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.42/0.58  thf('75', plain,
% 0.42/0.58      ((((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['73', '74'])).
% 0.42/0.58  thf('76', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((X0) = (k1_xboole_0))
% 0.42/0.58          | ((X1) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.58  thf('77', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.42/0.58  thf('78', plain,
% 0.42/0.58      ((((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['77'])).
% 0.42/0.58  thf('79', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.58  thf('80', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ sk_B @ X0) = (k1_xboole_0))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0))
% 0.42/0.58          | ((sk_E) = (k1_xboole_0))
% 0.42/0.58          | ((sk_F) = (k1_xboole_0))
% 0.42/0.58          | ((sk_A) = (k1_xboole_0))
% 0.42/0.58          | ((sk_A) = (sk_D)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['78', '79'])).
% 0.42/0.58  thf('81', plain,
% 0.42/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['58', '80'])).
% 0.42/0.58  thf('82', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('83', plain,
% 0.42/0.58      ((((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.42/0.58  thf('84', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.58  thf('85', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0))
% 0.42/0.58          | ((sk_E) = (k1_xboole_0))
% 0.42/0.58          | ((sk_F) = (k1_xboole_0))
% 0.42/0.58          | ((sk_A) = (sk_D)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['83', '84'])).
% 0.42/0.58  thf('86', plain,
% 0.42/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['57', '85'])).
% 0.42/0.58  thf('87', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('88', plain,
% 0.42/0.58      ((((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.42/0.58  thf('89', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.58      inference('sup+', [status(thm)], ['24', '26'])).
% 0.42/0.58  thf('90', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0))
% 0.42/0.58          | ((sk_E) = (k1_xboole_0))
% 0.42/0.58          | ((sk_A) = (sk_D)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['88', '89'])).
% 0.42/0.58  thf('91', plain,
% 0.42/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['56', '90'])).
% 0.42/0.58  thf('92', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('93', plain,
% 0.42/0.58      ((((sk_A) = (sk_D)) | ((sk_E) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.42/0.58  thf('94', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.58  thf('95', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (k1_xboole_0))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0))
% 0.42/0.58          | ((sk_A) = (sk_D)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['93', '94'])).
% 0.42/0.58  thf('96', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('97', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (sk_D))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['95', '96'])).
% 0.42/0.58  thf('98', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['97'])).
% 0.42/0.58  thf('99', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.58  thf('100', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ sk_D @ X1 @ X0) = (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['98', '99'])).
% 0.42/0.58  thf('101', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('102', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (sk_D)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['100', '101'])).
% 0.42/0.58  thf('103', plain, (((sk_A) = (sk_D))),
% 0.42/0.58      inference('simplify', [status(thm)], ['102'])).
% 0.42/0.58  thf('104', plain,
% 0.42/0.58      (((k3_zfmisc_1 @ sk_D @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.58      inference('demod', [status(thm)], ['55', '103'])).
% 0.42/0.58  thf('105', plain,
% 0.42/0.58      (((k3_zfmisc_1 @ sk_D @ sk_B @ sk_F) = (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.58      inference('demod', [status(thm)], ['55', '103'])).
% 0.42/0.58  thf('106', plain,
% 0.42/0.58      (![X3 : $i, X4 : $i]:
% 0.42/0.58         (((X3) = (k1_xboole_0))
% 0.42/0.58          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.42/0.58          | ((X4) = (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.42/0.58  thf('107', plain,
% 0.42/0.58      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['67'])).
% 0.42/0.58  thf('108', plain,
% 0.42/0.58      (![X3 : $i, X4 : $i]:
% 0.42/0.58         (((X3) = (k1_xboole_0))
% 0.42/0.58          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.42/0.58          | ((X4) = (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.42/0.58  thf('109', plain,
% 0.42/0.58      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['107', '108'])).
% 0.42/0.58  thf('110', plain, (((sk_A) = (sk_D))),
% 0.42/0.58      inference('simplify', [status(thm)], ['102'])).
% 0.42/0.58  thf('111', plain, (((sk_A) = (sk_D))),
% 0.42/0.58      inference('simplify', [status(thm)], ['102'])).
% 0.42/0.58  thf('112', plain,
% 0.42/0.58      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_E)) = (sk_B))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.42/0.58  thf('113', plain,
% 0.42/0.58      ((((sk_E) = (sk_B))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['106', '112'])).
% 0.42/0.58  thf('114', plain,
% 0.42/0.58      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (sk_B)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['113'])).
% 0.42/0.58  thf('115', plain,
% 0.42/0.58      ((((sk_A) != (sk_D)) | ((sk_B) != (sk_E)) | ((sk_C) != (sk_F)))),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('116', plain, ((((sk_B) != (sk_E))) <= (~ (((sk_B) = (sk_E))))),
% 0.42/0.58      inference('split', [status(esa)], ['115'])).
% 0.42/0.58  thf('117', plain, (((sk_C) = (sk_F))),
% 0.42/0.58      inference('simplify', [status(thm)], ['53'])).
% 0.42/0.58  thf('118', plain, ((((sk_C) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.42/0.58      inference('split', [status(esa)], ['115'])).
% 0.42/0.58  thf('119', plain, ((((sk_F) != (sk_F))) <= (~ (((sk_C) = (sk_F))))),
% 0.42/0.58      inference('sup-', [status(thm)], ['117', '118'])).
% 0.42/0.58  thf('120', plain, ((((sk_C) = (sk_F)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['119'])).
% 0.42/0.58  thf('121', plain, (((sk_A) = (sk_D))),
% 0.42/0.58      inference('simplify', [status(thm)], ['102'])).
% 0.42/0.58  thf('122', plain, ((((sk_A) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.42/0.58      inference('split', [status(esa)], ['115'])).
% 0.42/0.58  thf('123', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_A) = (sk_D))))),
% 0.42/0.58      inference('sup-', [status(thm)], ['121', '122'])).
% 0.42/0.58  thf('124', plain, ((((sk_A) = (sk_D)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['123'])).
% 0.42/0.58  thf('125', plain,
% 0.42/0.58      (~ (((sk_B) = (sk_E))) | ~ (((sk_A) = (sk_D))) | ~ (((sk_C) = (sk_F)))),
% 0.42/0.58      inference('split', [status(esa)], ['115'])).
% 0.42/0.58  thf('126', plain, (~ (((sk_B) = (sk_E)))),
% 0.42/0.58      inference('sat_resolution*', [status(thm)], ['120', '124', '125'])).
% 0.42/0.58  thf('127', plain, (((sk_B) != (sk_E))),
% 0.42/0.58      inference('simpl_trail', [status(thm)], ['116', '126'])).
% 0.42/0.58  thf('128', plain,
% 0.42/0.58      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify_reflect-', [status(thm)], ['114', '127'])).
% 0.42/0.58  thf('129', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((X0) = (k1_xboole_0))
% 0.42/0.58          | ((X1) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.58  thf('130', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['128', '129'])).
% 0.42/0.58  thf('131', plain,
% 0.42/0.58      ((((k2_zfmisc_1 @ sk_D @ sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['130'])).
% 0.42/0.58  thf('132', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((X0) = (k1_xboole_0))
% 0.42/0.58          | ((X1) = (k1_xboole_0))
% 0.42/0.58          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.42/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.58  thf('133', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['131', '132'])).
% 0.42/0.58  thf('134', plain,
% 0.42/0.58      ((((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_B) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify', [status(thm)], ['133'])).
% 0.42/0.58  thf('135', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.58  thf('136', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ sk_B @ X0) = (k1_xboole_0))
% 0.42/0.58          | ((sk_E) = (k1_xboole_0))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0))
% 0.42/0.58          | ((sk_F) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['134', '135'])).
% 0.42/0.58  thf('137', plain,
% 0.42/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['105', '136'])).
% 0.42/0.58  thf('138', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('139', plain,
% 0.42/0.58      ((((sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.42/0.58  thf('140', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.58      inference('sup+', [status(thm)], ['24', '26'])).
% 0.42/0.58  thf('141', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ X0 @ sk_F) = (k1_xboole_0))
% 0.42/0.58          | ((sk_E) = (k1_xboole_0))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['139', '140'])).
% 0.42/0.58  thf('142', plain,
% 0.42/0.58      ((((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) = (k1_xboole_0))
% 0.42/0.58        | ((sk_D) = (k1_xboole_0))
% 0.42/0.58        | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['104', '141'])).
% 0.42/0.58  thf('143', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('144', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 0.42/0.58      inference('simplify_reflect-', [status(thm)], ['142', '143'])).
% 0.42/0.58  thf('145', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.58  thf('146', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         (((k3_zfmisc_1 @ X1 @ sk_E @ X0) = (k1_xboole_0))
% 0.42/0.58          | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup+', [status(thm)], ['144', '145'])).
% 0.42/0.58  thf('147', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('148', plain,
% 0.42/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['146', '147'])).
% 0.42/0.58  thf('149', plain, (((sk_D) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['148'])).
% 0.42/0.58  thf('150', plain, (((k3_zfmisc_1 @ sk_D @ sk_E @ sk_F) != (sk_D))),
% 0.42/0.58      inference('demod', [status(thm)], ['2', '149'])).
% 0.42/0.58  thf('151', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 0.42/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.58  thf('152', plain, (((sk_D) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['148'])).
% 0.42/0.58  thf('153', plain, (((sk_D) = (k1_xboole_0))),
% 0.42/0.58      inference('simplify', [status(thm)], ['148'])).
% 0.42/0.58  thf('154', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ sk_D @ X1 @ X0) = (sk_D))),
% 0.42/0.58      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.42/0.58  thf('155', plain, (((sk_D) != (sk_D))),
% 0.42/0.58      inference('demod', [status(thm)], ['150', '154'])).
% 0.42/0.58  thf('156', plain, ($false), inference('simplify', [status(thm)], ['155'])).
% 0.42/0.58  
% 0.42/0.58  % SZS output end Refutation
% 0.42/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
