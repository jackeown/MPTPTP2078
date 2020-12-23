%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZlpkWOMPtD

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 201 expanded)
%              Number of leaves         :   23 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  945 (4628 expanded)
%              Number of equality atoms :  142 ( 696 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(t71_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = H ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = H ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X13
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k6_mcart_1 @ X10 @ X11 @ X12 @ X13 ) @ ( k7_mcart_1 @ X10 @ X11 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X14 @ X15 @ X17 @ X16 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k3_zfmisc_1 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('5',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X14 @ X15 @ X17 @ X16 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k3_zfmisc_1 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('12',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X14 @ X15 @ X17 @ X16 )
        = ( k2_mcart_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k3_zfmisc_1 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
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
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','9','16','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf(t28_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X9 = X7 )
      | ( ( k3_mcart_1 @ X5 @ X8 @ X9 )
       != ( k3_mcart_1 @ X4 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('30',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk3' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X9 ) ),
    inference(inj_rec,[status(thm)],['29'])).

thf('31',plain,
    ( ( '#_fresh_sk3' @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l44_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ! [G: $i] :
                        ( ( m1_subset_1 @ G @ C )
                       => ( D
                         != ( k3_mcart_1 @ E @ F @ G ) ) ) ) )
            & ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2
        = ( k3_mcart_1 @ ( sk_E @ X2 @ X3 @ X1 @ X0 ) @ ( sk_F @ X2 @ X3 @ X1 @ X0 ) @ ( sk_G @ X2 @ X3 @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('34',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('40',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X2 @ X3 @ X1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('42',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ sk_B )
      | ( sk_E_1
       != ( k3_mcart_1 @ X19 @ X18 @ X20 ) )
      | ( sk_D = X20 )
      | ~ ( m1_subset_1 @ X20 @ sk_C )
      | ~ ( m1_subset_1 @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X2 @ X3 @ X1 @ X0 ) @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X3 @ X1 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','56','63'])).

thf('65',plain,
    ( sk_D
    = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['38','65'])).

thf('67',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( '#_fresh_sk3' @ ( k3_mcart_1 @ X5 @ X8 @ X9 ) )
      = X9 ) ),
    inference(inj_rec,[status(thm)],['29'])).

thf('68',plain,
    ( ( '#_fresh_sk3' @ sk_E_1 )
    = sk_D ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_D
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['31','68'])).

thf('70',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('72',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZlpkWOMPtD
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:15:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 45 iterations in 0.026s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.19/0.48  thf('#_fresh_sk3_type', type, '#_fresh_sk3': $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.19/0.48  thf(t71_mcart_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.48       ( ( ![F:$i]:
% 0.19/0.48           ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.48             ( ![G:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.48                 ( ![H:$i]:
% 0.19/0.48                   ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.48                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.48                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.19/0.48         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.48           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.48           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.48        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.48          ( ( ![F:$i]:
% 0.19/0.48              ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.48                ( ![G:$i]:
% 0.19/0.48                  ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.48                    ( ![H:$i]:
% 0.19/0.48                      ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.48                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.48                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.19/0.48            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.48              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.48              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t48_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ~( ![D:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.48                 ( ( D ) =
% 0.19/0.48                   ( k3_mcart_1 @
% 0.19/0.48                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.48                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.48                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.48         (((X10) = (k1_xboole_0))
% 0.19/0.48          | ((X11) = (k1_xboole_0))
% 0.19/0.48          | ((X13)
% 0.19/0.48              = (k3_mcart_1 @ (k5_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.19/0.48                 (k6_mcart_1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.19/0.48                 (k7_mcart_1 @ X10 @ X11 @ X12 @ X13)))
% 0.19/0.48          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 0.19/0.48          | ((X12) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((sk_E_1)
% 0.19/0.48            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.19/0.48               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.19/0.48               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t50_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ~( ![D:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.48                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.48                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.48                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.48                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         (((X14) = (k1_xboole_0))
% 0.19/0.48          | ((X15) = (k1_xboole_0))
% 0.19/0.48          | ((k5_mcart_1 @ X14 @ X15 @ X17 @ X16)
% 0.19/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ X16)))
% 0.19/0.48          | ~ (m1_subset_1 @ X16 @ (k3_zfmisc_1 @ X14 @ X15 @ X17))
% 0.19/0.48          | ((X17) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.48            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.48         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         (((X14) = (k1_xboole_0))
% 0.19/0.48          | ((X15) = (k1_xboole_0))
% 0.19/0.48          | ((k6_mcart_1 @ X14 @ X15 @ X17 @ X16)
% 0.19/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X16)))
% 0.19/0.48          | ~ (m1_subset_1 @ X16 @ (k3_zfmisc_1 @ X14 @ X15 @ X17))
% 0.19/0.48          | ((X17) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.48         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         (((X14) = (k1_xboole_0))
% 0.19/0.48          | ((X15) = (k1_xboole_0))
% 0.19/0.48          | ((k7_mcart_1 @ X14 @ X15 @ X17 @ X16) = (k2_mcart_1 @ X16))
% 0.19/0.48          | ~ (m1_subset_1 @ X16 @ (k3_zfmisc_1 @ X14 @ X15 @ X17))
% 0.19/0.48          | ((X17) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('21', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((sk_E_1)
% 0.19/0.48            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.19/0.48               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ (k2_mcart_1 @ sk_E_1)))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['2', '9', '16', '23'])).
% 0.19/0.48  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('26', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('27', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (((sk_E_1)
% 0.19/0.48         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.19/0.48            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ (k2_mcart_1 @ sk_E_1)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 0.19/0.48  thf(t28_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.48     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.19/0.48       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.48         (((X9) = (X7))
% 0.19/0.48          | ((k3_mcart_1 @ X5 @ X8 @ X9) != (k3_mcart_1 @ X4 @ X6 @ X7)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.19/0.48         (('#_fresh_sk3' @ (k3_mcart_1 @ X5 @ X8 @ X9)) = (X9))),
% 0.19/0.48      inference('inj_rec', [status(thm)], ['29'])).
% 0.19/0.48  thf('31', plain, ((('#_fresh_sk3' @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['28', '30'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(l44_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ?[D:$i]:
% 0.19/0.48            ( ( ![E:$i]:
% 0.19/0.48                ( ( m1_subset_1 @ E @ A ) =>
% 0.19/0.48                  ( ![F:$i]:
% 0.19/0.48                    ( ( m1_subset_1 @ F @ B ) =>
% 0.19/0.48                      ( ![G:$i]:
% 0.19/0.48                        ( ( m1_subset_1 @ G @ C ) =>
% 0.19/0.48                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.19/0.48              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((X1) = (k1_xboole_0))
% 0.19/0.48          | ((X2)
% 0.19/0.48              = (k3_mcart_1 @ (sk_E @ X2 @ X3 @ X1 @ X0) @ 
% 0.19/0.48                 (sk_F @ X2 @ X3 @ X1 @ X0) @ (sk_G @ X2 @ X3 @ X1 @ X0)))
% 0.19/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.19/0.48          | ((X3) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((sk_E_1)
% 0.19/0.48            = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.48               (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.48               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.48  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('36', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('37', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (((sk_E_1)
% 0.19/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.48            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (((sk_E_1)
% 0.19/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.48            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.48            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((X1) = (k1_xboole_0))
% 0.19/0.48          | (m1_subset_1 @ (sk_F @ X2 @ X3 @ X1 @ X0) @ X1)
% 0.19/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.19/0.48          | ((X3) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.48  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('45', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['42', '43', '44', '45'])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X18 @ sk_B)
% 0.19/0.48          | ((sk_E_1) != (k3_mcart_1 @ X19 @ X18 @ X20))
% 0.19/0.48          | ((sk_D) = (X20))
% 0.19/0.48          | ~ (m1_subset_1 @ X20 @ sk_C)
% 0.19/0.48          | ~ (m1_subset_1 @ X19 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.19/0.48          | ((sk_D) = (X1))
% 0.19/0.48          | ((sk_E_1)
% 0.19/0.48              != (k3_mcart_1 @ X0 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      ((((sk_E_1) != (sk_E_1))
% 0.19/0.48        | ((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.19/0.48        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.48        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['39', '48'])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((X1) = (k1_xboole_0))
% 0.19/0.48          | (m1_subset_1 @ (sk_G @ X2 @ X3 @ X1 @ X0) @ X3)
% 0.19/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.19/0.48          | ((X3) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.48  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('54', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['52', '53', '54', '55'])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('58', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((X1) = (k1_xboole_0))
% 0.19/0.48          | (m1_subset_1 @ (sk_E @ X2 @ X3 @ X1 @ X0) @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.19/0.48          | ((X3) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.48  thf('59', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.48        | ((sk_B) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.48  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('63', plain,
% 0.19/0.48      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.19/0.48  thf('64', plain,
% 0.19/0.48      ((((sk_E_1) != (sk_E_1))
% 0.19/0.48        | ((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['49', '56', '63'])).
% 0.19/0.48  thf('65', plain, (((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['64'])).
% 0.19/0.48  thf('66', plain,
% 0.19/0.48      (((sk_E_1)
% 0.19/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.48            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D))),
% 0.19/0.48      inference('demod', [status(thm)], ['38', '65'])).
% 0.19/0.48  thf('67', plain,
% 0.19/0.48      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.19/0.48         (('#_fresh_sk3' @ (k3_mcart_1 @ X5 @ X8 @ X9)) = (X9))),
% 0.19/0.48      inference('inj_rec', [status(thm)], ['29'])).
% 0.19/0.48  thf('68', plain, ((('#_fresh_sk3' @ sk_E_1) = (sk_D))),
% 0.19/0.48      inference('sup+', [status(thm)], ['66', '67'])).
% 0.19/0.48  thf('69', plain, (((sk_D) = (k2_mcart_1 @ sk_E_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['31', '68'])).
% 0.19/0.48  thf('70', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('71', plain,
% 0.19/0.48      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.19/0.48  thf('72', plain, (((sk_D) != (k2_mcart_1 @ sk_E_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['70', '71'])).
% 0.19/0.48  thf('73', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['69', '72'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
