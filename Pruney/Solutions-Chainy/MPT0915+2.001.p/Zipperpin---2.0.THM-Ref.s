%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VOBAsURhNN

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 163 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  913 (5591 expanded)
%              Number of equality atoms :  134 ( 835 expanded)
%              Maximal formula depth    :   27 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(t75_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ( E != k1_xboole_0 )
        & ( F != k1_xboole_0 )
        & ? [G: $i] :
            ( ? [H: $i] :
                ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ G )
                      = ( k5_mcart_1 @ D @ E @ F @ H ) )
                    & ( ( k6_mcart_1 @ A @ B @ C @ G )
                      = ( k6_mcart_1 @ D @ E @ F @ H ) )
                    & ( ( k7_mcart_1 @ A @ B @ C @ G )
                      = ( k7_mcart_1 @ D @ E @ F @ H ) ) )
                & ( G = H )
                & ( m1_subset_1 @ H @ ( k3_zfmisc_1 @ D @ E @ F ) ) )
            & ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ( E != k1_xboole_0 )
          & ( F != k1_xboole_0 )
          & ? [G: $i] :
              ( ? [H: $i] :
                  ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ G )
                        = ( k5_mcart_1 @ D @ E @ F @ H ) )
                      & ( ( k6_mcart_1 @ A @ B @ C @ G )
                        = ( k6_mcart_1 @ D @ E @ F @ H ) )
                      & ( ( k7_mcart_1 @ A @ B @ C @ G )
                        = ( k7_mcart_1 @ D @ E @ F @ H ) ) )
                  & ( G = H )
                  & ( m1_subset_1 @ H @ ( k3_zfmisc_1 @ D @ E @ F ) ) )
              & ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_mcart_1])).

thf('0',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_H @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X0 @ X1 @ X3 @ X2 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('8',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_E != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_F != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X0 @ X1 @ X3 @ X2 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    = ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X0 @ X1 @ X3 @ X2 )
        = ( k2_mcart_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('28',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_E != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_F != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G )
    = ( k2_mcart_1 @ sk_G ) ),
    inference('simplify_reflect-',[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k2_mcart_1 @ sk_G ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X0 @ X1 @ X3 @ X2 )
        = ( k2_mcart_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('39',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    = ( k2_mcart_1 @ sk_G ) ),
    inference('simplify_reflect-',[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( ( k2_mcart_1 @ sk_G )
     != ( k2_mcart_1 @ sk_G ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    = ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
     != ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
 != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H ) ),
    inference('sat_resolution*',[status(thm)],['25','45','46'])).

thf('48',plain,(
    ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
 != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['3','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X0 @ X1 @ X3 @ X2 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) )
 != ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X0 @ X1 @ X3 @ X2 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('59',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_E != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_F != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VOBAsURhNN
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 29 iterations in 0.015s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.48  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.48  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(t75_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( E ) != ( k1_xboole_0 ) ) & ( ( F ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ?[G:$i]:
% 0.20/0.48            ( ( ?[H:$i]:
% 0.20/0.48                ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ G ) =
% 0.20/0.48                         ( k5_mcart_1 @ D @ E @ F @ H ) ) & 
% 0.20/0.48                       ( ( k6_mcart_1 @ A @ B @ C @ G ) =
% 0.20/0.48                         ( k6_mcart_1 @ D @ E @ F @ H ) ) & 
% 0.20/0.48                       ( ( k7_mcart_1 @ A @ B @ C @ G ) =
% 0.20/0.48                         ( k7_mcart_1 @ D @ E @ F @ H ) ) ) ) & 
% 0.20/0.48                  ( ( G ) = ( H ) ) & 
% 0.20/0.48                  ( m1_subset_1 @ H @ ( k3_zfmisc_1 @ D @ E @ F ) ) ) ) & 
% 0.20/0.48              ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.48        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48             ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48             ( ( E ) != ( k1_xboole_0 ) ) & ( ( F ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48             ( ?[G:$i]:
% 0.20/0.48               ( ( ?[H:$i]:
% 0.20/0.48                   ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ G ) =
% 0.20/0.48                            ( k5_mcart_1 @ D @ E @ F @ H ) ) & 
% 0.20/0.48                          ( ( k6_mcart_1 @ A @ B @ C @ G ) =
% 0.20/0.48                            ( k6_mcart_1 @ D @ E @ F @ H ) ) & 
% 0.20/0.48                          ( ( k7_mcart_1 @ A @ B @ C @ G ) =
% 0.20/0.48                            ( k7_mcart_1 @ D @ E @ F @ H ) ) ) ) & 
% 0.20/0.48                     ( ( G ) = ( H ) ) & 
% 0.20/0.48                     ( m1_subset_1 @ H @ ( k3_zfmisc_1 @ D @ E @ F ) ) ) ) & 
% 0.20/0.48                 ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t75_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          != (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))
% 0.20/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48            != (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))
% 0.20/0.48        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48            != (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          != (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain, (((sk_G) = (sk_H))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          != (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((m1_subset_1 @ sk_H @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain, (((sk_G) = (sk_H))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(t50_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ~( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.48                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.48                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.48                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.48                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k5_mcart_1 @ X0 @ X1 @ X3 @ X2)
% 0.20/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ X2)))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.20/0.48          | ((X3) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((((sk_F) = (k1_xboole_0))
% 0.20/0.48        | ((k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.20/0.48            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.48        | ((sk_E) = (k1_xboole_0))
% 0.20/0.48        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, (((sk_E) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain, (((sk_F) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.20/0.48         = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['8', '9', '10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          != (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('14', plain, (((sk_G) = (sk_H))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          != (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          != (k1_mcart_1 @ (k1_mcart_1 @ sk_G))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.48  thf('17', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k5_mcart_1 @ X0 @ X1 @ X3 @ X2)
% 0.20/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ X2)))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.20/0.48          | ((X3) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48         = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_G))
% 0.20/0.48          != (k1_mcart_1 @ (k1_mcart_1 @ sk_G))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          = (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  thf('26', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k7_mcart_1 @ X0 @ X1 @ X3 @ X2) = (k2_mcart_1 @ X2))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.20/0.48          | ((X3) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((((sk_F) = (k1_xboole_0))
% 0.20/0.48        | ((k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.20/0.48        | ((sk_E) = (k1_xboole_0))
% 0.20/0.48        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, (((sk_E) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, (((sk_F) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G) = (k2_mcart_1 @ sk_G))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['28', '29', '30', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          != (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('34', plain, (((sk_G) = (sk_H))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          != (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) != (k2_mcart_1 @ sk_G)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.48  thf('37', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k7_mcart_1 @ X0 @ X1 @ X3 @ X2) = (k2_mcart_1 @ X2))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.20/0.48          | ((X3) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['39', '40', '41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      ((((k2_mcart_1 @ sk_G) != (k2_mcart_1 @ sk_G)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48                = (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      ((((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          = (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          = (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))) | 
% 0.20/0.48       ~
% 0.20/0.48       (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          = (k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H))) | 
% 0.20/0.48       ~
% 0.20/0.48       (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          = (k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48          = (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_H)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['25', '45', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48         != (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['3', '47'])).
% 0.20/0.48  thf('49', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k6_mcart_1 @ X0 @ X1 @ X3 @ X2)
% 0.20/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X2)))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.20/0.48          | ((X3) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('54', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.48         = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['51', '52', '53', '54'])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (((k2_mcart_1 @ (k1_mcart_1 @ sk_G))
% 0.20/0.48         != (k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.20/0.48      inference('demod', [status(thm)], ['48', '55'])).
% 0.20/0.48  thf('57', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k6_mcart_1 @ X0 @ X1 @ X3 @ X2)
% 0.20/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X2)))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.20/0.48          | ((X3) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      ((((sk_F) = (k1_xboole_0))
% 0.20/0.48        | ((k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.20/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.48        | ((sk_E) = (k1_xboole_0))
% 0.20/0.48        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.48  thf('60', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('61', plain, (((sk_E) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('62', plain, (((sk_F) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (((k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.20/0.48         = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (((k2_mcart_1 @ (k1_mcart_1 @ sk_G))
% 0.20/0.48         != (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.20/0.48      inference('demod', [status(thm)], ['56', '63'])).
% 0.20/0.48  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
