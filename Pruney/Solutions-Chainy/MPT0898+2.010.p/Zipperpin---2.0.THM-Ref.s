%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GO11E9txiD

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 754 expanded)
%              Number of leaves         :   11 ( 224 expanded)
%              Depth                    :   26
%              Number of atoms          :  746 (8935 expanded)
%              Number of equality atoms :  139 (1315 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('5',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
       != ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) )
      | ( X13 = X16 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X0 = X4 )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ X6 @ X5 @ X4 ) )
      | ( X0 = X4 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B )
        = k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X0 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_B = sk_A ) ),
    inference(eq_res,[status(thm)],['14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('25',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_B @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( X8 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X7 @ X8 @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('37',plain,(
    ! [X7: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_B @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_B = k1_xboole_0 ),
    inference(condensation,[status(thm)],['42'])).

thf('44',plain,(
    sk_B = k1_xboole_0 ),
    inference(condensation,[status(thm)],['42'])).

thf('45',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['22','43','44'])).

thf('46',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_A @ X0 )
      = ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','37'])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(condensation,[status(thm)],['42'])).

thf('52',plain,(
    sk_B = k1_xboole_0 ),
    inference(condensation,[status(thm)],['42'])).

thf('53',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ sk_A @ X0 )
      = sk_B ) ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
       != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference(condensation,[status(thm)],['42'])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(condensation,[status(thm)],['42'])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference(condensation,[status(thm)],['42'])).

thf('59',plain,(
    sk_B = k1_xboole_0 ),
    inference(condensation,[status(thm)],['42'])).

thf('60',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
       != sk_B )
      | ( X9 = sk_B )
      | ( X8 = sk_B )
      | ( X7 = sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] : ( X0 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GO11E9txiD
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 139 iterations in 0.103s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(d3_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.20/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.20/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.55      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(d4_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.20/0.55       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.55           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(t58_mcart_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.20/0.55       ( ( A ) = ( B ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.20/0.55          ( ( A ) = ( B ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.55         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.55           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(t37_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.55     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.55       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         (((k3_zfmisc_1 @ X11 @ X12 @ X13) = (k1_xboole_0))
% 0.20/0.55          | ((k3_zfmisc_1 @ X11 @ X12 @ X13) != (k3_zfmisc_1 @ X14 @ X15 @ X16))
% 0.20/0.55          | ((X13) = (X16)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.20/0.55          | ((X0) = (X4))
% 0.20/0.55          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.55           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ X6 @ X5 @ X4))
% 0.20/0.55          | ((X0) = (X4))
% 0.20/0.55          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.55            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B) = (k1_xboole_0))
% 0.20/0.55          | ((sk_B) = (X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.55         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.55            != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.55          | ((sk_B) = (X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.55            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((sk_B) = (X0))
% 0.20/0.55          | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (sk_A)))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['14'])).
% 0.20/0.55  thf('16', plain, (((sk_A) != (sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.55           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(t35_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.55       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (((k3_zfmisc_1 @ X7 @ X8 @ X9) != (k1_xboole_0))
% 0.20/0.55          | ((X9) = (k1_xboole_0))
% 0.20/0.55          | ((X8) = (k1_xboole_0))
% 0.20/0.55          | ((X7) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.55          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.20/0.55          | ((X1) = (k1_xboole_0))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.20/0.55         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.55          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.20/0.55          | ((X1) = (k1_xboole_0))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.20/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k3_zfmisc_1 @ sk_B @ sk_B @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.20/0.55          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.55         (((X10) != (k1_xboole_0))
% 0.20/0.55          | ((k3_zfmisc_1 @ X7 @ X8 @ X10) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X7 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.55      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ k1_xboole_0 @ X0)
% 0.20/0.55           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.55         (((X8) != (k1_xboole_0))
% 0.20/0.55          | ((k3_zfmisc_1 @ X7 @ X8 @ X10) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X7 : $i, X10 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X7 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k3_zfmisc_1 @ sk_B @ sk_B @ X0) = (k1_xboole_0))
% 0.20/0.55          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['31', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (((k3_zfmisc_1 @ X7 @ X8 @ X9) != (k1_xboole_0))
% 0.20/0.55          | ((X9) = (k1_xboole_0))
% 0.20/0.55          | ((X8) = (k1_xboole_0))
% 0.20/0.55          | ((X7) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.55          | ((sk_B) = (k1_xboole_0))
% 0.20/0.55          | ((sk_B) = (k1_xboole_0))
% 0.20/0.55          | ((sk_B) = (k1_xboole_0))
% 0.20/0.55          | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.55  thf('43', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('condensation', [status(thm)], ['42'])).
% 0.20/0.55  thf('44', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('condensation', [status(thm)], ['42'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '43', '44'])).
% 0.20/0.55  thf('46', plain, (((sk_A) != (sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('47', plain, (((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.20/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ sk_A @ sk_A @ X0) = (k2_zfmisc_1 @ sk_B @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '37'])).
% 0.20/0.55  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('condensation', [status(thm)], ['42'])).
% 0.20/0.55  thf('52', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('condensation', [status(thm)], ['42'])).
% 0.20/0.55  thf('53', plain, (![X0 : $i]: ((sk_B) = (k2_zfmisc_1 @ sk_B @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.20/0.55  thf('54', plain, (![X0 : $i]: ((k3_zfmisc_1 @ sk_A @ sk_A @ X0) = (sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['49', '53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (((k3_zfmisc_1 @ X7 @ X8 @ X9) != (k1_xboole_0))
% 0.20/0.55          | ((X9) = (k1_xboole_0))
% 0.20/0.55          | ((X8) = (k1_xboole_0))
% 0.20/0.55          | ((X7) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.55  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('condensation', [status(thm)], ['42'])).
% 0.20/0.55  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('condensation', [status(thm)], ['42'])).
% 0.20/0.55  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('condensation', [status(thm)], ['42'])).
% 0.20/0.55  thf('59', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('condensation', [status(thm)], ['42'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (((k3_zfmisc_1 @ X7 @ X8 @ X9) != (sk_B))
% 0.20/0.55          | ((X9) = (sk_B))
% 0.20/0.55          | ((X8) = (sk_B))
% 0.20/0.55          | ((X7) = (sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((sk_B) != (sk_B))
% 0.20/0.55          | ((sk_A) = (sk_B))
% 0.20/0.55          | ((sk_A) = (sk_B))
% 0.20/0.55          | ((X0) = (sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['54', '60'])).
% 0.20/0.55  thf('62', plain, (![X0 : $i]: (((X0) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.55  thf('63', plain, (((sk_A) != (sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('64', plain, (![X0 : $i]: ((X0) = (sk_B))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.20/0.55  thf('65', plain, (((sk_A) != (sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('66', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.55  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
