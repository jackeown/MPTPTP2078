%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0888+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qhJGQLqqOE

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 709 expanded)
%              Number of leaves         :   22 ( 218 expanded)
%              Depth                    :   18
%              Number of atoms          : 1366 (16879 expanded)
%              Number of equality atoms :  145 (2046 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_G_3_type,type,(
    sk_G_3: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_F_3_type,type,(
    sk_F_3: $i > $i > $i > $i > $i )).

thf(t48_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( D
                  = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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

thf('1',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X38
        = ( k3_mcart_1 @ ( sk_E @ X38 @ X39 @ X37 @ X36 ) @ ( sk_F_3 @ X38 @ X39 @ X37 @ X36 ) @ ( sk_G_3 @ X38 @ X39 @ X37 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k3_zfmisc_1 @ X36 @ X37 @ X39 ) )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf(d5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( E
                      = ( k5_mcart_1 @ A @ B @ C @ D ) )
                  <=> ! [F: $i,G: $i,H: $i] :
                        ( ( D
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( E = F ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( X2
       != ( k5_mcart_1 @ X0 @ X1 @ X3 @ X4 ) )
      | ( X2 = X5 )
      | ( X4
       != ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d5_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X3: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( ( k5_mcart_1 @ X0 @ X1 @ X3 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) )
        = X5 )
      | ~ ( m1_subset_1 @ ( k5_mcart_1 @ X0 @ X1 @ X3 @ ( k3_mcart_1 @ X5 @ X6 @ X7 ) ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k5_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ X2 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('13',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k5_mcart_1 @ X2 @ X1 @ X0 @ sk_D ) @ X2 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X24 @ X25 @ X26 @ X27 ) @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k3_zfmisc_1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('18',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

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
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf(d6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ! [E: $i] :
                  ( ( m1_subset_1 @ E @ B )
                 => ( ( E
                      = ( k6_mcart_1 @ A @ B @ C @ D ) )
                  <=> ! [F: $i,G: $i,H: $i] :
                        ( ( D
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( E = G ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( X10
       != ( k6_mcart_1 @ X8 @ X9 @ X11 @ X12 ) )
      | ( X10 = X13 )
      | ( X12
       != ( k3_mcart_1 @ X14 @ X13 @ X15 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k3_zfmisc_1 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d6_mcart_1])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X11: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X14 @ X13 @ X15 ) @ ( k3_zfmisc_1 @ X8 @ X9 @ X11 ) )
      | ( ( k6_mcart_1 @ X8 @ X9 @ X11 @ ( k3_mcart_1 @ X14 @ X13 @ X15 ) )
        = X13 )
      | ~ ( m1_subset_1 @ ( k6_mcart_1 @ X8 @ X9 @ X11 @ ( k3_mcart_1 @ X14 @ X13 @ X15 ) ) @ X9 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ X1 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('31',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_D ) @ X1 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X28 @ X29 @ X30 @ X31 ) @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('36',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( sk_F_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','41'])).

thf(d7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ! [E: $i] :
                  ( ( m1_subset_1 @ E @ C )
                 => ( ( E
                      = ( k7_mcart_1 @ A @ B @ C @ D ) )
                  <=> ! [F: $i,G: $i,H: $i] :
                        ( ( D
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( E = H ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ X19 )
      | ( X18
       != ( k7_mcart_1 @ X16 @ X17 @ X19 @ X20 ) )
      | ( X18 = X21 )
      | ( X20
       != ( k3_mcart_1 @ X22 @ X23 @ X21 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_mcart_1])).

thf('46',plain,(
    ! [X16: $i,X17: $i,X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X22 @ X23 @ X21 ) @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( ( k7_mcart_1 @ X16 @ X17 @ X19 @ ( k3_mcart_1 @ X22 @ X23 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ ( k7_mcart_1 @ X16 @ X17 @ X19 @ ( k3_mcart_1 @ X22 @ X23 @ X21 ) ) @ X19 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k7_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ X0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','41'])).

thf('49',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','41'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k7_mcart_1 @ X2 @ X1 @ X0 @ sk_D ) @ X0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X32 @ X33 @ X34 @ X35 ) @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k3_zfmisc_1 @ X32 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('54',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( sk_G_3 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','59'])).

thf('61',plain,(
    sk_D
 != ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).


%------------------------------------------------------------------------------
