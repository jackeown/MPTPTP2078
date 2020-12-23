%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KptIt8pJ8w

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
