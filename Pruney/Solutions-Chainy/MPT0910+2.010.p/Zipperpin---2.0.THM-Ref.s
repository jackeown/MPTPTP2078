%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ETTbhzrQdd

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 500 expanded)
%              Number of leaves         :   28 ( 170 expanded)
%              Depth                    :   16
%              Number of atoms          : 1631 (9986 expanded)
%              Number of equality atoms :  217 (1389 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t70_mcart_1,conjecture,(
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
                     => ( D = G ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = G ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X27
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X24 @ X25 @ X26 @ X27 ) @ ( k6_mcart_1 @ X24 @ X25 @ X26 @ X27 ) @ ( k7_mcart_1 @ X24 @ X25 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k3_zfmisc_1 @ X24 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X27
        = ( k4_tarski @ ( k4_tarski @ ( k5_mcart_1 @ X24 @ X25 @ X26 @ X27 ) @ ( k6_mcart_1 @ X24 @ X25 @ X26 @ X27 ) ) @ ( k7_mcart_1 @ X24 @ X25 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X28 @ X29 @ X31 @ X30 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X28 @ X29 @ X31 @ X30 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

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
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X28 @ X29 @ X31 @ X30 )
        = ( k2_mcart_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X28 @ X29 @ X31 @ X30 )
        = ( k2_mcart_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','16','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X28 @ X29 @ X31 @ X30 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X28 @ X29 @ X31 @ X30 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16
        = ( k3_mcart_1 @ ( sk_E @ X16 @ X17 @ X15 @ X14 ) @ ( sk_F @ X16 @ X17 @ X15 @ X14 ) @ ( sk_G @ X16 @ X17 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k3_zfmisc_1 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16
        = ( k4_tarski @ ( k4_tarski @ ( sk_E @ X16 @ X17 @ X15 @ X14 ) @ ( sk_F @ X16 @ X17 @ X15 @ X14 ) ) @ ( sk_G @ X16 @ X17 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47','48','49'])).

thf(t28_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X19 = X18 )
      | ( ( k3_mcart_1 @ X19 @ X22 @ X23 )
       != ( k3_mcart_1 @ X18 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('53',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X19 @ X22 @ X23 ) )
      = X19 ) ),
    inference(inj_rec,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('55',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ ( k4_tarski @ X19 @ X22 ) @ X23 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( '#_fresh_sk1' @ sk_E_1 )
    = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf('57',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( '#_fresh_sk1' @ sk_E_1 ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','56'])).

thf('58',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( '#_fresh_sk1' @ sk_E_1 ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','56'])).

thf('59',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X22 = X20 )
      | ( ( k3_mcart_1 @ X19 @ X22 @ X23 )
       != ( k3_mcart_1 @ X18 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('60',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X19 @ X22 @ X23 ) )
      = X22 ) ),
    inference(inj_rec,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('62',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( k4_tarski @ X19 @ X22 ) @ X23 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( '#_fresh_sk2' @ sk_E_1 )
    = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( '#_fresh_sk1' @ sk_E_1 ) @ ( '#_fresh_sk2' @ sk_E_1 ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X22 = X20 )
      | ( ( k3_mcart_1 @ X19 @ X22 @ X23 )
       != ( k3_mcart_1 @ X18 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('68',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X22 = X20 )
      | ( ( k4_tarski @ ( k4_tarski @ X19 @ X22 ) @ X23 )
       != ( k4_tarski @ ( k4_tarski @ X18 @ X20 ) @ X21 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) )
      | ( ( '#_fresh_sk2' @ sk_E_1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47','48','49'])).

thf('71',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ sk_B )
      | ( sk_D = X32 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X33 @ X32 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_C )
      | ~ ( m1_subset_1 @ X33 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('73',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ sk_B )
      | ( sk_D = X32 )
      | ( sk_E_1
       != ( k4_tarski @ ( k4_tarski @ X33 @ X32 ) @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_C )
      | ~ ( m1_subset_1 @ X33 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X16 @ X17 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k3_zfmisc_1 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('77',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('78',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X16 @ X17 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','83'])).

thf('85',plain,
    ( ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( '#_fresh_sk1' @ sk_E_1 )
    = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf('87',plain,
    ( ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( '#_fresh_sk1' @ sk_E_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( '#_fresh_sk2' @ sk_E_1 )
    = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('89',plain,
    ( ( sk_D
      = ( '#_fresh_sk2' @ sk_E_1 ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( '#_fresh_sk1' @ sk_E_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('91',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X16 @ X17 @ X15 @ X14 ) @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k3_zfmisc_1 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('92',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('93',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X16 @ X17 @ X15 @ X14 ) @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['94','95','96','97'])).

thf('99',plain,
    ( ( sk_D
      = ( '#_fresh_sk2' @ sk_E_1 ) )
    | ~ ( m1_subset_1 @ ( '#_fresh_sk1' @ sk_E_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_E_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('101',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X16 @ X17 @ X15 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k3_zfmisc_1 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('102',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('103',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X16 @ X17 @ X15 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( '#_fresh_sk1' @ sk_E_1 )
    = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf('106',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( '#_fresh_sk1' @ sk_E_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ ( '#_fresh_sk1' @ sk_E_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( sk_D
    = ( '#_fresh_sk2' @ sk_E_1 ) ),
    inference(demod,[status(thm)],['99','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) )
      | ( sk_D = X1 ) ) ),
    inference(demod,[status(thm)],['69','111'])).

thf('113',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','112'])).

thf('114',plain,
    ( sk_D
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('117',plain,(
    sk_D
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ETTbhzrQdd
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:24:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 201 iterations in 0.082s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.19/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.53  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.53  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.53  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.53  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.19/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.53  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(t70_mcart_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.53       ( ( ![F:$i]:
% 0.19/0.53           ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.53             ( ![G:$i]:
% 0.19/0.53               ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.53                 ( ![H:$i]:
% 0.19/0.53                   ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.53                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.53                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.19/0.53         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.53           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.53           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.53        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.53          ( ( ![F:$i]:
% 0.19/0.53              ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.53                ( ![G:$i]:
% 0.19/0.53                  ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.53                    ( ![H:$i]:
% 0.19/0.53                      ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.53                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.53                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.19/0.53            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.53              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.53              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d3_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.19/0.53       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ 
% 0.19/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf(t48_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ~( ![D:$i]:
% 0.19/0.53               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.53                 ( ( D ) =
% 0.19/0.53                   ( k3_mcart_1 @
% 0.19/0.53                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.53                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.53                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.53         (((X24) = (k1_xboole_0))
% 0.19/0.53          | ((X25) = (k1_xboole_0))
% 0.19/0.53          | ((X27)
% 0.19/0.53              = (k3_mcart_1 @ (k5_mcart_1 @ X24 @ X25 @ X26 @ X27) @ 
% 0.19/0.53                 (k6_mcart_1 @ X24 @ X25 @ X26 @ X27) @ 
% 0.19/0.53                 (k7_mcart_1 @ X24 @ X25 @ X26 @ X27)))
% 0.19/0.53          | ~ (m1_subset_1 @ X27 @ (k3_zfmisc_1 @ X24 @ X25 @ X26))
% 0.19/0.53          | ((X26) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.19/0.53  thf(d3_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.53         (((X24) = (k1_xboole_0))
% 0.19/0.53          | ((X25) = (k1_xboole_0))
% 0.19/0.53          | ((X27)
% 0.19/0.53              = (k4_tarski @ 
% 0.19/0.53                 (k4_tarski @ (k5_mcart_1 @ X24 @ X25 @ X26 @ X27) @ 
% 0.19/0.53                  (k6_mcart_1 @ X24 @ X25 @ X26 @ X27)) @ 
% 0.19/0.53                 (k7_mcart_1 @ X24 @ X25 @ X26 @ X27)))
% 0.19/0.53          | ~ (m1_subset_1 @ X27 @ 
% 0.19/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25) @ X26))
% 0.19/0.53          | ((X26) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((sk_E_1)
% 0.19/0.53            = (k4_tarski @ 
% 0.19/0.53               (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.19/0.53                (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)) @ 
% 0.19/0.53               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '6'])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ 
% 0.19/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf(t50_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ~( ![D:$i]:
% 0.19/0.53               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.53                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.53                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.53                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.53                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.53         (((X28) = (k1_xboole_0))
% 0.19/0.53          | ((X29) = (k1_xboole_0))
% 0.19/0.53          | ((k6_mcart_1 @ X28 @ X29 @ X31 @ X30)
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X30)))
% 0.19/0.53          | ~ (m1_subset_1 @ X30 @ (k3_zfmisc_1 @ X28 @ X29 @ X31))
% 0.19/0.53          | ((X31) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.53         (((X28) = (k1_xboole_0))
% 0.19/0.53          | ((X29) = (k1_xboole_0))
% 0.19/0.53          | ((k6_mcart_1 @ X28 @ X29 @ X31 @ X30)
% 0.19/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X30)))
% 0.19/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.19/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X31))
% 0.19/0.53          | ((X31) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['8', '11'])).
% 0.19/0.53  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ 
% 0.19/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.53         (((X28) = (k1_xboole_0))
% 0.19/0.53          | ((X29) = (k1_xboole_0))
% 0.19/0.53          | ((k7_mcart_1 @ X28 @ X29 @ X31 @ X30) = (k2_mcart_1 @ X30))
% 0.19/0.53          | ~ (m1_subset_1 @ X30 @ (k3_zfmisc_1 @ X28 @ X29 @ X31))
% 0.19/0.53          | ((X31) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.53         (((X28) = (k1_xboole_0))
% 0.19/0.53          | ((X29) = (k1_xboole_0))
% 0.19/0.53          | ((k7_mcart_1 @ X28 @ X29 @ X31 @ X30) = (k2_mcart_1 @ X30))
% 0.19/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.19/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X31))
% 0.19/0.53          | ((X31) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['17', '20'])).
% 0.19/0.53  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['21', '22', '23', '24'])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((sk_E_1)
% 0.19/0.53            = (k4_tarski @ 
% 0.19/0.53               (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.19/0.53                (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) @ 
% 0.19/0.53               (k2_mcart_1 @ sk_E_1)))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['7', '16', '25'])).
% 0.19/0.53  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('28', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (((sk_E_1)
% 0.19/0.53         = (k4_tarski @ 
% 0.19/0.53            (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ 
% 0.19/0.53             (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) @ 
% 0.19/0.53            (k2_mcart_1 @ sk_E_1)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ 
% 0.19/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.53         (((X28) = (k1_xboole_0))
% 0.19/0.53          | ((X29) = (k1_xboole_0))
% 0.19/0.53          | ((k5_mcart_1 @ X28 @ X29 @ X31 @ X30)
% 0.19/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X30)))
% 0.19/0.53          | ~ (m1_subset_1 @ X30 @ (k3_zfmisc_1 @ X28 @ X29 @ X31))
% 0.19/0.53          | ((X31) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.53         (((X28) = (k1_xboole_0))
% 0.19/0.53          | ((X29) = (k1_xboole_0))
% 0.19/0.53          | ((k5_mcart_1 @ X28 @ X29 @ X31 @ X30)
% 0.19/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X30)))
% 0.19/0.53          | ~ (m1_subset_1 @ X30 @ 
% 0.19/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X31))
% 0.19/0.53          | ((X31) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.53            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['31', '34'])).
% 0.19/0.53  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('38', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.53         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['35', '36', '37', '38'])).
% 0.19/0.53  thf('40', plain,
% 0.19/0.53      (((sk_E_1)
% 0.19/0.53         = (k4_tarski @ 
% 0.19/0.53            (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.19/0.53             (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) @ 
% 0.19/0.53            (k2_mcart_1 @ sk_E_1)))),
% 0.19/0.53      inference('demod', [status(thm)], ['30', '39'])).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ 
% 0.19/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf(l44_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ?[D:$i]:
% 0.19/0.53            ( ( ![E:$i]:
% 0.19/0.53                ( ( m1_subset_1 @ E @ A ) =>
% 0.19/0.53                  ( ![F:$i]:
% 0.19/0.53                    ( ( m1_subset_1 @ F @ B ) =>
% 0.19/0.53                      ( ![G:$i]:
% 0.19/0.53                        ( ( m1_subset_1 @ G @ C ) =>
% 0.19/0.53                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.19/0.53              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((X14) = (k1_xboole_0))
% 0.19/0.53          | ((X15) = (k1_xboole_0))
% 0.19/0.53          | ((X16)
% 0.19/0.53              = (k3_mcart_1 @ (sk_E @ X16 @ X17 @ X15 @ X14) @ 
% 0.19/0.53                 (sk_F @ X16 @ X17 @ X15 @ X14) @ 
% 0.19/0.53                 (sk_G @ X16 @ X17 @ X15 @ X14)))
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ (k3_zfmisc_1 @ X14 @ X15 @ X17))
% 0.19/0.53          | ((X17) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((X14) = (k1_xboole_0))
% 0.19/0.53          | ((X15) = (k1_xboole_0))
% 0.19/0.53          | ((X16)
% 0.19/0.53              = (k4_tarski @ 
% 0.19/0.53                 (k4_tarski @ (sk_E @ X16 @ X17 @ X15 @ X14) @ 
% 0.19/0.53                  (sk_F @ X16 @ X17 @ X15 @ X14)) @ 
% 0.19/0.53                 (sk_G @ X16 @ X17 @ X15 @ X14)))
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ 
% 0.19/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X17))
% 0.19/0.53          | ((X17) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | ((sk_E_1)
% 0.19/0.53            = (k4_tarski @ 
% 0.19/0.53               (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53                (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.53               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['41', '45'])).
% 0.19/0.53  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('48', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('49', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('50', plain,
% 0.19/0.53      (((sk_E_1)
% 0.19/0.53         = (k4_tarski @ 
% 0.19/0.53            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.53            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['46', '47', '48', '49'])).
% 0.19/0.53  thf('51', plain,
% 0.19/0.53      (((sk_E_1)
% 0.19/0.53         = (k4_tarski @ 
% 0.19/0.53            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.53            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['46', '47', '48', '49'])).
% 0.19/0.53  thf(t28_mcart_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.53     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.19/0.53       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 0.19/0.53  thf('52', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         (((X19) = (X18))
% 0.19/0.53          | ((k3_mcart_1 @ X19 @ X22 @ X23) != (k3_mcart_1 @ X18 @ X20 @ X21)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         (('#_fresh_sk1' @ (k3_mcart_1 @ X19 @ X22 @ X23)) = (X19))),
% 0.19/0.53      inference('inj_rec', [status(thm)], ['52'])).
% 0.19/0.53  thf('54', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('55', plain,
% 0.19/0.53      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         (('#_fresh_sk1' @ (k4_tarski @ (k4_tarski @ X19 @ X22) @ X23)) = (X19))),
% 0.19/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.53  thf('56', plain,
% 0.19/0.53      ((('#_fresh_sk1' @ sk_E_1) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['51', '55'])).
% 0.19/0.53  thf('57', plain,
% 0.19/0.53      (((sk_E_1)
% 0.19/0.53         = (k4_tarski @ 
% 0.19/0.53            (k4_tarski @ ('#_fresh_sk1' @ sk_E_1) @ 
% 0.19/0.53             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.53            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['50', '56'])).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      (((sk_E_1)
% 0.19/0.53         = (k4_tarski @ 
% 0.19/0.53            (k4_tarski @ ('#_fresh_sk1' @ sk_E_1) @ 
% 0.19/0.53             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.53            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['50', '56'])).
% 0.19/0.53  thf('59', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         (((X22) = (X20))
% 0.19/0.53          | ((k3_mcart_1 @ X19 @ X22 @ X23) != (k3_mcart_1 @ X18 @ X20 @ X21)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.19/0.53  thf('60', plain,
% 0.19/0.53      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         (('#_fresh_sk2' @ (k3_mcart_1 @ X19 @ X22 @ X23)) = (X22))),
% 0.19/0.53      inference('inj_rec', [status(thm)], ['59'])).
% 0.19/0.53  thf('61', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('62', plain,
% 0.19/0.53      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         (('#_fresh_sk2' @ (k4_tarski @ (k4_tarski @ X19 @ X22) @ X23)) = (X22))),
% 0.19/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.53  thf('63', plain,
% 0.19/0.53      ((('#_fresh_sk2' @ sk_E_1) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['58', '62'])).
% 0.19/0.53  thf('64', plain,
% 0.19/0.53      (((sk_E_1)
% 0.19/0.53         = (k4_tarski @ 
% 0.19/0.53            (k4_tarski @ ('#_fresh_sk1' @ sk_E_1) @ ('#_fresh_sk2' @ sk_E_1)) @ 
% 0.19/0.53            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['57', '63'])).
% 0.19/0.53  thf('65', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         (((X22) = (X20))
% 0.19/0.53          | ((k3_mcart_1 @ X19 @ X22 @ X23) != (k3_mcart_1 @ X18 @ X20 @ X21)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.19/0.53  thf('66', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('67', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('68', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.53         (((X22) = (X20))
% 0.19/0.53          | ((k4_tarski @ (k4_tarski @ X19 @ X22) @ X23)
% 0.19/0.53              != (k4_tarski @ (k4_tarski @ X18 @ X20) @ X21)))),
% 0.19/0.53      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.19/0.53  thf('69', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (((sk_E_1) != (k4_tarski @ (k4_tarski @ X2 @ X1) @ X0))
% 0.19/0.53          | (('#_fresh_sk2' @ sk_E_1) = (X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['64', '68'])).
% 0.19/0.53  thf('70', plain,
% 0.19/0.53      (((sk_E_1)
% 0.19/0.53         = (k4_tarski @ 
% 0.19/0.53            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.53             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.53            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['46', '47', '48', '49'])).
% 0.19/0.53  thf('71', plain,
% 0.19/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X32 @ sk_B)
% 0.19/0.53          | ((sk_D) = (X32))
% 0.19/0.53          | ((sk_E_1) != (k3_mcart_1 @ X33 @ X32 @ X34))
% 0.19/0.53          | ~ (m1_subset_1 @ X34 @ sk_C)
% 0.19/0.53          | ~ (m1_subset_1 @ X33 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('72', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.53  thf('73', plain,
% 0.19/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X32 @ sk_B)
% 0.19/0.53          | ((sk_D) = (X32))
% 0.19/0.53          | ((sk_E_1) != (k4_tarski @ (k4_tarski @ X33 @ X32) @ X34))
% 0.19/0.53          | ~ (m1_subset_1 @ X34 @ sk_C)
% 0.19/0.53          | ~ (m1_subset_1 @ X33 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['71', '72'])).
% 0.19/0.53  thf('74', plain,
% 0.19/0.53      ((((sk_E_1) != (sk_E_1))
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.53        | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['70', '73'])).
% 0.19/0.53  thf('75', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ 
% 0.19/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf('76', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((X14) = (k1_xboole_0))
% 0.19/0.53          | ((X15) = (k1_xboole_0))
% 0.19/0.53          | (m1_subset_1 @ (sk_F @ X16 @ X17 @ X15 @ X14) @ X15)
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ (k3_zfmisc_1 @ X14 @ X15 @ X17))
% 0.19/0.53          | ((X17) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.53  thf('77', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('78', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((X14) = (k1_xboole_0))
% 0.19/0.53          | ((X15) = (k1_xboole_0))
% 0.19/0.53          | (m1_subset_1 @ (sk_F @ X16 @ X17 @ X15 @ X14) @ X15)
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ 
% 0.19/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X17))
% 0.19/0.53          | ((X17) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.53  thf('79', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['75', '78'])).
% 0.19/0.53  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('81', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('82', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('83', plain,
% 0.19/0.53      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['79', '80', '81', '82'])).
% 0.19/0.53  thf('84', plain,
% 0.19/0.53      ((((sk_E_1) != (sk_E_1))
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.53        | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['74', '83'])).
% 0.19/0.53  thf('85', plain,
% 0.19/0.53      ((((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.53      inference('simplify', [status(thm)], ['84'])).
% 0.19/0.53  thf('86', plain,
% 0.19/0.53      ((('#_fresh_sk1' @ sk_E_1) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['51', '55'])).
% 0.19/0.53  thf('87', plain,
% 0.19/0.53      ((((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.53        | ~ (m1_subset_1 @ ('#_fresh_sk1' @ sk_E_1) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['85', '86'])).
% 0.19/0.53  thf('88', plain,
% 0.19/0.53      ((('#_fresh_sk2' @ sk_E_1) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['58', '62'])).
% 0.19/0.53  thf('89', plain,
% 0.19/0.53      ((((sk_D) = ('#_fresh_sk2' @ sk_E_1))
% 0.19/0.53        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.53        | ~ (m1_subset_1 @ ('#_fresh_sk1' @ sk_E_1) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['87', '88'])).
% 0.19/0.53  thf('90', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ 
% 0.19/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf('91', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((X14) = (k1_xboole_0))
% 0.19/0.53          | ((X15) = (k1_xboole_0))
% 0.19/0.53          | (m1_subset_1 @ (sk_G @ X16 @ X17 @ X15 @ X14) @ X17)
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ (k3_zfmisc_1 @ X14 @ X15 @ X17))
% 0.19/0.53          | ((X17) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.53  thf('92', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('93', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((X14) = (k1_xboole_0))
% 0.19/0.53          | ((X15) = (k1_xboole_0))
% 0.19/0.53          | (m1_subset_1 @ (sk_G @ X16 @ X17 @ X15 @ X14) @ X17)
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ 
% 0.19/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X17))
% 0.19/0.53          | ((X17) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['91', '92'])).
% 0.19/0.53  thf('94', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['90', '93'])).
% 0.19/0.53  thf('95', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('96', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('97', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('98', plain,
% 0.19/0.53      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['94', '95', '96', '97'])).
% 0.19/0.53  thf('99', plain,
% 0.19/0.53      ((((sk_D) = ('#_fresh_sk2' @ sk_E_1))
% 0.19/0.53        | ~ (m1_subset_1 @ ('#_fresh_sk1' @ sk_E_1) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['89', '98'])).
% 0.19/0.53  thf('100', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_E_1 @ 
% 0.19/0.53        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf('101', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((X14) = (k1_xboole_0))
% 0.19/0.53          | ((X15) = (k1_xboole_0))
% 0.19/0.53          | (m1_subset_1 @ (sk_E @ X16 @ X17 @ X15 @ X14) @ X14)
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ (k3_zfmisc_1 @ X14 @ X15 @ X17))
% 0.19/0.53          | ((X17) = (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.19/0.53  thf('102', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.53         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.53  thf('103', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.53         (((X14) = (k1_xboole_0))
% 0.19/0.53          | ((X15) = (k1_xboole_0))
% 0.19/0.53          | (m1_subset_1 @ (sk_E @ X16 @ X17 @ X15 @ X14) @ X14)
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ 
% 0.19/0.53               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X17))
% 0.19/0.53          | ((X17) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['101', '102'])).
% 0.19/0.53  thf('104', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['100', '103'])).
% 0.19/0.53  thf('105', plain,
% 0.19/0.53      ((('#_fresh_sk1' @ sk_E_1) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.19/0.53      inference('sup+', [status(thm)], ['51', '55'])).
% 0.19/0.53  thf('106', plain,
% 0.19/0.53      ((((sk_C) = (k1_xboole_0))
% 0.19/0.53        | (m1_subset_1 @ ('#_fresh_sk1' @ sk_E_1) @ sk_A)
% 0.19/0.53        | ((sk_B) = (k1_xboole_0))
% 0.19/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['104', '105'])).
% 0.19/0.53  thf('107', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('109', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('110', plain, ((m1_subset_1 @ ('#_fresh_sk1' @ sk_E_1) @ sk_A)),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)],
% 0.19/0.53                ['106', '107', '108', '109'])).
% 0.19/0.53  thf('111', plain, (((sk_D) = ('#_fresh_sk2' @ sk_E_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['99', '110'])).
% 0.19/0.53  thf('112', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (((sk_E_1) != (k4_tarski @ (k4_tarski @ X2 @ X1) @ X0))
% 0.19/0.53          | ((sk_D) = (X1)))),
% 0.19/0.53      inference('demod', [status(thm)], ['69', '111'])).
% 0.19/0.53  thf('113', plain,
% 0.19/0.53      ((((sk_E_1) != (sk_E_1))
% 0.19/0.53        | ((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['40', '112'])).
% 0.19/0.53  thf('114', plain, (((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['113'])).
% 0.19/0.53  thf('115', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('116', plain,
% 0.19/0.53      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.19/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.19/0.53  thf('117', plain, (((sk_D) != (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.19/0.53      inference('demod', [status(thm)], ['115', '116'])).
% 0.19/0.53  thf('118', plain, ($false),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['114', '117'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
