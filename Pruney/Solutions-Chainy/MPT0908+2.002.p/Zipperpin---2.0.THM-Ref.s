%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rrSSNip0Kx

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 130 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  863 (2856 expanded)
%              Number of equality atoms :  138 ( 462 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t68_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ? [E: $i,F: $i,G: $i] :
              ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                    = E )
                  & ( ( k6_mcart_1 @ A @ B @ C @ D )
                    = F )
                  & ( ( k7_mcart_1 @ A @ B @ C @ D )
                    = G ) )
              & ( D
                = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ~ ( ( A != k1_xboole_0 )
            & ( B != k1_xboole_0 )
            & ( C != k1_xboole_0 )
            & ? [E: $i,F: $i,G: $i] :
                ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                      = E )
                    & ( ( k6_mcart_1 @ A @ B @ C @ D )
                      = F )
                    & ( ( k7_mcart_1 @ A @ B @ C @ D )
                      = G ) )
                & ( D
                  = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ? [D: $i] :
            ( ? [E: $i,F: $i,G: $i] :
                ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                      = E )
                    & ( ( k6_mcart_1 @ A @ B @ C @ D )
                      = F )
                    & ( ( k7_mcart_1 @ A @ B @ C @ D )
                      = G ) )
                & ( D
                  = ( k3_mcart_1 @ E @ F @ G ) ) )
            & ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X8
       != ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
      | ( ( k5_mcart_1 @ X3 @ X4 @ X9 @ X8 )
        = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X3 @ X4 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) @ ( k3_zfmisc_1 @ X3 @ X4 @ X9 ) )
      | ( ( k5_mcart_1 @ X3 @ X4 @ X9 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
        = X5 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X9 ) )
      | ( ( k5_mcart_1 @ X3 @ X4 @ X9 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
        = X5 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) )
        = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = sk_E )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('17',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X8
       != ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
      | ( ( k7_mcart_1 @ X3 @ X4 @ X9 @ X8 )
        = X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X3 @ X4 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) @ ( k3_zfmisc_1 @ X3 @ X4 @ X9 ) )
      | ( ( k7_mcart_1 @ X3 @ X4 @ X9 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
        = X7 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X9 ) )
      | ( ( k7_mcart_1 @ X3 @ X4 @ X9 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
        = X7 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) )
        = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = sk_G )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = sk_G )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_G ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference(split,[status(esa)],['14'])).

thf('31',plain,
    ( ( sk_G != sk_G )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_G ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('34',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X8
       != ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
      | ( ( k6_mcart_1 @ X3 @ X4 @ X9 @ X8 )
        = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X3 @ X4 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) @ ( k3_zfmisc_1 @ X3 @ X4 @ X9 ) )
      | ( ( k6_mcart_1 @ X3 @ X4 @ X9 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
        = X6 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X9 ) )
      | ( ( k6_mcart_1 @ X3 @ X4 @ X9 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
        = X6 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = sk_F )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = sk_F )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_F ),
    inference('simplify_reflect-',[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['14'])).

thf('48',plain,
    ( ( sk_F != sk_F )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = sk_F ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_E )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_F )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
     != sk_G ) ),
    inference(split,[status(esa)],['14'])).

thf('51',plain,(
    ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['32','49','50'])).

thf('52',plain,(
    ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['15','51'])).

thf('53',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rrSSNip0Kx
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 20 iterations in 0.016s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(t68_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49            ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49            ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.49              ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.49                     ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.49                     ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.49                ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49               ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49               ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.49                 ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.49                        ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.49                        ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.49                   ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t68_mcart_1])).
% 0.21/0.49  thf('0', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d3_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t47_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ?[D:$i]:
% 0.21/0.49            ( ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.49                ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.49                       ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.49                       ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.49                  ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) & 
% 0.21/0.49              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X8) != (k3_mcart_1 @ X5 @ X6 @ X7))
% 0.21/0.49          | ((k5_mcart_1 @ X3 @ X4 @ X9 @ X8) = (X5))
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X3 @ X4 @ X9))
% 0.21/0.49          | ((X9) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.49         (((X9) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X5 @ X6 @ X7) @ 
% 0.21/0.49               (k3_zfmisc_1 @ X3 @ X4 @ X9))
% 0.21/0.49          | ((k5_mcart_1 @ X3 @ X4 @ X9 @ (k3_mcart_1 @ X5 @ X6 @ X7)) = (X5))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X3) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.49         (((X9) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X5 @ X6 @ X7) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X9))
% 0.21/0.49          | ((k5_mcart_1 @ X3 @ X4 @ X9 @ (k3_mcart_1 @ X5 @ X6 @ X7)) = (X5))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X3) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k5_mcart_1 @ X2 @ X1 @ X0 @ (k3_mcart_1 @ sk_E @ sk_F @ sk_G))
% 0.21/0.49              = (sk_E))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.49  thf('9', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k5_mcart_1 @ X2 @ X1 @ X0 @ sk_D) = (sk_E))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '10'])).
% 0.21/0.49  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_E))
% 0.21/0.49        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_F))
% 0.21/0.49        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_G)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_E)))
% 0.21/0.49         <= (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))))),
% 0.21/0.49      inference('split', [status(esa)], ['14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('17', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X8) != (k3_mcart_1 @ X5 @ X6 @ X7))
% 0.21/0.49          | ((k7_mcart_1 @ X3 @ X4 @ X9 @ X8) = (X7))
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X3 @ X4 @ X9))
% 0.21/0.49          | ((X9) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.49         (((X9) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X5 @ X6 @ X7) @ 
% 0.21/0.49               (k3_zfmisc_1 @ X3 @ X4 @ X9))
% 0.21/0.49          | ((k7_mcart_1 @ X3 @ X4 @ X9 @ (k3_mcart_1 @ X5 @ X6 @ X7)) = (X7))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X3) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.49         (((X9) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X5 @ X6 @ X7) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X9))
% 0.21/0.49          | ((k7_mcart_1 @ X3 @ X4 @ X9 @ (k3_mcart_1 @ X5 @ X6 @ X7)) = (X7))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X3) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ (k3_mcart_1 @ sk_E @ sk_F @ sk_G))
% 0.21/0.49              = (sk_G))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '21'])).
% 0.21/0.49  thf('23', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ sk_D) = (sk_G))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '24'])).
% 0.21/0.49  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain, (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_G)))
% 0.21/0.49         <= (~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))))),
% 0.21/0.49      inference('split', [status(esa)], ['14'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      ((((sk_G) != (sk_G)))
% 0.21/0.49         <= (~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain, ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('34', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (((X3) = (k1_xboole_0))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X8) != (k3_mcart_1 @ X5 @ X6 @ X7))
% 0.21/0.49          | ((k6_mcart_1 @ X3 @ X4 @ X9 @ X8) = (X6))
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X3 @ X4 @ X9))
% 0.21/0.49          | ((X9) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.49         (((X9) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X5 @ X6 @ X7) @ 
% 0.21/0.49               (k3_zfmisc_1 @ X3 @ X4 @ X9))
% 0.21/0.49          | ((k6_mcart_1 @ X3 @ X4 @ X9 @ (k3_mcart_1 @ X5 @ X6 @ X7)) = (X6))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X3) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.49         (((X9) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X5 @ X6 @ X7) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X9))
% 0.21/0.49          | ((k6_mcart_1 @ X3 @ X4 @ X9 @ (k3_mcart_1 @ X5 @ X6 @ X7)) = (X6))
% 0.21/0.49          | ((X4) = (k1_xboole_0))
% 0.21/0.49          | ((X3) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ (k3_mcart_1 @ sk_E @ sk_F @ sk_G))
% 0.21/0.49              = (sk_F))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '38'])).
% 0.21/0.49  thf('40', plain, (((sk_D) = (k3_mcart_1 @ sk_E @ sk_F @ sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_D @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ sk_D) = (sk_F))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '41'])).
% 0.21/0.49  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain, (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['42', '43', '44', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_F)))
% 0.21/0.49         <= (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))))),
% 0.21/0.49      inference('split', [status(esa)], ['14'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      ((((sk_F) != (sk_F)))
% 0.21/0.49         <= (~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain, ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E))) | 
% 0.21/0.49       ~ (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_F))) | 
% 0.21/0.49       ~ (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_G)))),
% 0.21/0.49      inference('split', [status(esa)], ['14'])).
% 0.21/0.49  thf('51', plain, (~ (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (sk_E)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['32', '49', '50'])).
% 0.21/0.49  thf('52', plain, (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) != (sk_E))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['15', '51'])).
% 0.21/0.49  thf('53', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('54', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['11', '12', '13', '52', '53'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
