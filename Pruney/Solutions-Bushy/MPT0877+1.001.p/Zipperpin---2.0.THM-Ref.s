%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0877+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SWu6L2DO11

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 (4234 expanded)
%              Number of leaves         :   11 (1061 expanded)
%              Depth                    :   39
%              Number of atoms          :  847 (63892 expanded)
%              Number of equality atoms :  193 (13584 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

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
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) )
      | ( X4 = X9 ) ) ),
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

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( X3 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X0 @ X1 @ X3 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_C )
        = k1_xboole_0 )
      | ( sk_C = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( X1 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X0 @ X1 @ X3 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_F )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf('21',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X0 @ X1 @ X3 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_C = sk_F ) ) ),
    inference('sup+',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup+',[status(thm)],['4','25'])).

thf('27',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('28',plain,(
    sk_C = sk_F ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','28'])).

thf('30',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','28'])).

thf('31',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','28'])).

thf('32',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','28'])).

thf('33',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['3','28'])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference(eq_res,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('sup+',[status(thm)],['32','38'])).

thf('40',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('41',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B = sk_E )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('sup+',[status(thm)],['31','43'])).

thf('45',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('46',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_B = sk_E ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_B = sk_E ) ),
    inference('sup+',[status(thm)],['30','48'])).

thf('50',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('51',plain,(
    sk_B = sk_E ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_E @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['29','51'])).

thf('53',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_E @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['29','51'])).

thf('54',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_E @ sk_F )
    = ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['29','51'])).

thf('55',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) )
      | ( X6 = X7 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_A = X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = sk_D ) ),
    inference(eq_res,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_A != sk_D )
   <= ( sk_A != sk_D ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,(
    sk_C = sk_F ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('61',plain,
    ( ( sk_C != sk_F )
   <= ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['58'])).

thf('62',plain,
    ( ( sk_F != sk_F )
   <= ( sk_C != sk_F ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_C = sk_F ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_B = sk_E ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('65',plain,
    ( ( sk_B != sk_E )
   <= ( sk_B != sk_E ) ),
    inference(split,[status(esa)],['58'])).

thf('66',plain,
    ( ( sk_E != sk_E )
   <= ( sk_B != sk_E ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B = sk_E ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( sk_A != sk_D )
    | ( sk_B != sk_E )
    | ( sk_C != sk_F ) ),
    inference(split,[status(esa)],['58'])).

thf('69',plain,(
    sk_A != sk_D ),
    inference('sat_resolution*',[status(thm)],['63','67','68'])).

thf('70',plain,(
    sk_A != sk_D ),
    inference(simpl_trail,[status(thm)],['59','69'])).

thf('71',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['57','70'])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','73'])).

thf('75',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('76',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_F )
        = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
      = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','78'])).

thf('80',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('81',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F )
 != sk_E ),
    inference(demod,[status(thm)],['2','81'])).

thf('83',plain,(
    ! [X0: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('84',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('85',plain,(
    sk_E = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('86',plain,(
    ! [X0: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X0 @ sk_E @ X3 )
      = sk_E ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['82','86'])).

thf('88',plain,(
    $false ),
    inference(simplify,[status(thm)],['87'])).


%------------------------------------------------------------------------------
