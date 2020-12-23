%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QpQnPVkMdP

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:34 EST 2020

% Result     : Theorem 2.64s
% Output     : Refutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  218 (9452 expanded)
%              Number of leaves         :   39 (2862 expanded)
%              Depth                    :   39
%              Number of atoms          : 2392 (193580 expanded)
%              Number of equality atoms :  319 (29427 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i > $i )).

thf(sk_F_2_type,type,(
    sk_F_2: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X59: $i] :
      ( ( X59 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X59 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B_1 @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t51_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( D
                 != ( k5_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k6_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( D
                   != ( k5_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k6_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_mcart_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
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

thf('7',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X52 @ X53 @ X55 @ X54 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X54 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k3_zfmisc_1 @ X52 @ X53 @ X55 ) )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('8',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) )
    | ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) )
    | ( sk_D_3
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_D_3
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
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

thf('17',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X45
        = ( k3_mcart_1 @ ( sk_E_2 @ X45 @ X46 @ X44 @ X43 ) @ ( sk_F_2 @ X45 @ X46 @ X44 @ X43 ) @ ( sk_G @ X45 @ X46 @ X44 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k3_zfmisc_1 @ X43 @ X44 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('18',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_3
      = ( k3_mcart_1 @ ( sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_G @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_G @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_G @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('24',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_mcart_1 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('25',plain,(
    ! [X56: $i,X58: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X56 @ X58 ) )
      = X58 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_mcart_1 @ sk_D_3 )
    = ( sk_G @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k2_mcart_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k2_mcart_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('30',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_mcart_1 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('31',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X56 @ X57 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X56 @ X57 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) )
    = ( sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k2_mcart_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k2_mcart_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('39',plain,(
    ! [X56: $i,X58: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X56 @ X58 ) )
      = X58 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) )
    = ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( k2_mcart_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( sk_D_3
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ sk_D_3 @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['15','42'])).

thf('44',plain,
    ( ( sk_D_3
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ sk_D_3 @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['15','42'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('46',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_mcart_1 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X3 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ sk_D_3 @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ X0 ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_D_3
      = ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( r2_hidden @ X61 @ X59 )
      | ( ( sk_B_1 @ X59 )
       != ( k4_tarski @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ X0 )
         != sk_D_3 )
        | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_D_3 ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_D_3 ) )
          = k1_xboole_0 )
        | ( ( sk_B_1 @ ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_D_3 ) ) )
         != sk_D_3 ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['5','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_D_3 )
        | ( ( sk_B_1 @ ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_D_3 ) ) )
          = ( k1_mcart_1 @ sk_D_3 ) )
        | ( ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_D_3 ) )
          = k1_xboole_0 )
        | ( ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_D_3 ) )
          = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['3','52'])).

thf('54',plain,
    ( ( ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) ) )
        = ( k1_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_D_3
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('56',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( k2_mcart_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('58',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( r2_hidden @ X60 @ X59 )
      | ( ( sk_B_1 @ X59 )
       != ( k4_tarski @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_B_1 @ X3 )
       != ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ X0 )
       != ( k1_mcart_1 @ sk_D_3 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_3 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B_1 @ X0 )
         != ( k1_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( ( k1_mcart_1 @ sk_D_3 )
       != ( k1_mcart_1 @ sk_D_3 ) )
      | ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X3 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('64',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( ( k1_mcart_1 @ sk_D_3 )
       != ( k1_mcart_1 @ sk_D_3 ) )
      | ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
        = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['62','64'])).

thf('66',plain,
    ( ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
      = k1_xboole_0 )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('68',plain,
    ( ( r2_hidden @ sk_D_3 @ k1_xboole_0 )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X52 @ X53 @ X55 @ X54 )
        = ( k2_mcart_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k3_zfmisc_1 @ X52 @ X53 @ X55 ) )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('71',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 )
      = ( k2_mcart_1 @ sk_D_3 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 )
    = ( k2_mcart_1 @ sk_D_3 ) ),
    inference('simplify_reflect-',[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( sk_D_3
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) )
   <= ( sk_D_3
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('77',plain,
    ( ( sk_D_3
      = ( k2_mcart_1 @ sk_D_3 ) )
   <= ( sk_D_3
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k2_mcart_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('79',plain,
    ( ( sk_D_3
      = ( k3_mcart_1 @ ( sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_D_3 ) )
   <= ( sk_D_3
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_mcart_1 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('81',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47
       != ( k2_mcart_1 @ X47 ) )
      | ( X47
       != ( k4_tarski @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('82',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k4_tarski @ X48 @ X49 )
     != ( k2_mcart_1 @ ( k4_tarski @ X48 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X56: $i,X58: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X56 @ X58 ) )
      = X58 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('84',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k4_tarski @ X48 @ X49 )
     != X49 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,(
    sk_D_3
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ),
    inference('simplify_reflect-',[status(thm)],['79','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B_1 @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('88',plain,(
    m1_subset_1 @ sk_D_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X52 @ X53 @ X55 @ X54 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X54 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k3_zfmisc_1 @ X52 @ X53 @ X55 ) )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('90',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('96',plain,
    ( ( sk_D_3
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_D_3
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( k2_mcart_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('98',plain,
    ( ( sk_D_3
      = ( k3_mcart_1 @ sk_D_3 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('100',plain,
    ( ( ( k1_mcart_1 @ sk_D_3 )
      = ( k4_tarski @ sk_D_3 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_D_3
      = ( k3_mcart_1 @ sk_D_3 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('102',plain,
    ( ( ( k1_mcart_1 @ sk_D_3 )
      = ( k4_tarski @ sk_D_3 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('103',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_mcart_1 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ sk_D_3 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ X0 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_D_3
      = ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_mcart_1 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ ( k1_mcart_1 @ sk_D_3 ) @ ( k2_mcart_1 @ sk_D_3 ) @ X0 )
        = ( k4_tarski @ sk_D_3 @ X0 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('109',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k3_mcart_1 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ X37 @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('110',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( r2_hidden @ X61 @ X59 )
      | ( ( sk_B_1 @ X59 )
       != ( k4_tarski @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_B_1 @ X3 )
       != ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) )
       != ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_B_1 @ ( k2_tarski @ ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ ( k2_mcart_1 @ sk_D_3 ) ) @ X1 ) )
         != ( k4_tarski @ sk_D_3 @ X0 ) )
        | ( ( k2_tarski @ ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ ( k2_mcart_1 @ sk_D_3 ) ) @ X1 )
          = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,
    ( ( sk_D_3
      = ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('115',plain,
    ( ( sk_D_3
      = ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('116',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_B_1 @ ( k2_tarski @ sk_D_3 @ X1 ) )
         != ( k4_tarski @ sk_D_3 @ X0 ) )
        | ( ( k2_tarski @ sk_D_3 @ X1 )
          = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ ( k2_tarski @ sk_D_3 @ X0 ) )
         != ( k1_mcart_1 @ sk_D_3 ) )
        | ( ( k2_tarski @ sk_D_3 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['100','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( X0
         != ( k1_mcart_1 @ sk_D_3 ) )
        | ( ( sk_B_1 @ ( k2_tarski @ sk_D_3 @ X0 ) )
          = sk_D_3 )
        | ( ( k2_tarski @ sk_D_3 @ X0 )
          = k1_xboole_0 )
        | ( ( k2_tarski @ sk_D_3 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['87','117'])).

thf('119',plain,
    ( ( ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) ) )
        = sk_D_3 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('121',plain,
    ( ( sk_D_3
      = ( k4_tarski @ ( k1_mcart_1 @ sk_D_3 ) @ ( k2_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('122',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( r2_hidden @ X61 @ X59 )
      | ( ( sk_B_1 @ X59 )
       != ( k4_tarski @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ X0 )
         != sk_D_3 )
        | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_D_3 ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_D_3 ) )
          = k1_xboole_0 )
        | ( ( sk_B_1 @ ( k2_tarski @ X0 @ ( k1_mcart_1 @ sk_D_3 ) ) )
         != sk_D_3 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,
    ( ( ( sk_D_3 != sk_D_3 )
      | ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
        = k1_xboole_0 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,
    ( ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
      = k1_xboole_0 )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('128',plain,
    ( ( r2_hidden @ sk_D_3 @ k1_xboole_0 )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('130',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X28 @ X30 ) @ X31 )
        = ( k2_tarski @ X28 @ X30 ) )
      | ( r2_hidden @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('131',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X2 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X2 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(condensation,[status(thm)],['134'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('136',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( X8
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('137',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ( zip_tseitin_0 @ X7 @ X6 @ ( k4_tarski @ X6 @ X7 ) @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ X0 @ sk_D_3 @ ( k4_tarski @ sk_D_3 @ X0 ) @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['128','138'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('140',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('141',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['139','141'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('143',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_zfmisc_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('144',plain,(
    ! [X24: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X0 ) @ k1_xboole_0 )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['142','144'])).

thf('146',plain,
    ( ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
      = k1_xboole_0 )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('147',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_D_3 )
        | ( X0
          = ( k1_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( ( k4_tarski @ sk_D_3 @ X0 )
          = ( k1_mcart_1 @ sk_D_3 ) )
        | ( ( k4_tarski @ sk_D_3 @ X0 )
          = sk_D_3 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47
       != ( k1_mcart_1 @ X47 ) )
      | ( X47
       != ( k4_tarski @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('151',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k4_tarski @ X48 @ X49 )
     != ( k1_mcart_1 @ ( k4_tarski @ X48 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X56 @ X57 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('153',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k4_tarski @ X48 @ X49 )
     != X48 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ( k4_tarski @ sk_D_3 @ X0 )
        = ( k1_mcart_1 @ sk_D_3 ) )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['149','153'])).

thf('155',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k4_tarski @ X48 @ X49 )
     != X49 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ( k1_mcart_1 @ sk_D_3 )
       != X0 )
   <= ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    sk_D_3
 != ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) )
    | ( sk_D_3
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) )
    | ( sk_D_3
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('159',plain,
    ( sk_D_3
    = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ),
    inference('sat_resolution*',[status(thm)],['86','157','158'])).

thf('160',plain,(
    r2_hidden @ sk_D_3 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['68','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('162',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_D_3 @ ( k4_tarski @ sk_D_3 @ X0 ) @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('164',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X24: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['143'])).

thf('166',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k2_tarski @ sk_D_3 @ ( k1_mcart_1 @ sk_D_3 ) )
      = k1_xboole_0 )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('168',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('169',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_D_3 )
        | ( X0
          = ( k1_mcart_1 @ sk_D_3 ) ) )
   <= ( sk_D_3
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( sk_D_3
    = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3 ) ),
    inference('sat_resolution*',[status(thm)],['86','157','158'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = sk_D_3 )
      | ( X0
        = ( k1_mcart_1 @ sk_D_3 ) ) ) ),
    inference(simpl_trail,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k4_tarski @ sk_D_3 @ X0 )
        = ( k1_mcart_1 @ sk_D_3 ) )
      | ( ( k4_tarski @ sk_D_3 @ X0 )
        = sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['166','171'])).

thf('173',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k4_tarski @ X48 @ X49 )
     != X48 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k4_tarski @ sk_D_3 @ X0 )
      = ( k1_mcart_1 @ sk_D_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k4_tarski @ X48 @ X49 )
     != X49 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k1_mcart_1 @ sk_D_3 )
     != X0 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    $false ),
    inference(simplify,[status(thm)],['176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QpQnPVkMdP
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.64/2.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.64/2.84  % Solved by: fo/fo7.sh
% 2.64/2.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.64/2.84  % done 3121 iterations in 2.386s
% 2.64/2.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.64/2.84  % SZS output start Refutation
% 2.64/2.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.64/2.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.64/2.84  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 2.64/2.84  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 2.64/2.84  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 2.64/2.84  thf(sk_D_3_type, type, sk_D_3: $i).
% 2.64/2.84  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.64/2.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.64/2.84  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.64/2.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 2.64/2.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.64/2.84  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 2.64/2.84  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 2.64/2.84  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 2.64/2.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.64/2.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.64/2.84  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 2.64/2.84  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.64/2.84  thf(sk_E_2_type, type, sk_E_2: $i > $i > $i > $i > $i).
% 2.64/2.84  thf(sk_F_2_type, type, sk_F_2: $i > $i > $i > $i > $i).
% 2.64/2.84  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 2.64/2.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.64/2.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.64/2.84  thf(sk_A_type, type, sk_A: $i).
% 2.64/2.84  thf(t9_mcart_1, axiom,
% 2.64/2.84    (![A:$i]:
% 2.64/2.84     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84          ( ![B:$i]:
% 2.64/2.84            ( ~( ( r2_hidden @ B @ A ) & 
% 2.64/2.84                 ( ![C:$i,D:$i]:
% 2.64/2.84                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 2.64/2.84                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 2.64/2.84  thf('0', plain,
% 2.64/2.84      (![X59 : $i]:
% 2.64/2.84         (((X59) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X59) @ X59))),
% 2.64/2.84      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.64/2.84  thf(d2_tarski, axiom,
% 2.64/2.84    (![A:$i,B:$i,C:$i]:
% 2.64/2.84     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.64/2.84       ( ![D:$i]:
% 2.64/2.84         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.64/2.84  thf('1', plain,
% 2.64/2.84      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.64/2.84         (~ (r2_hidden @ X4 @ X2)
% 2.64/2.84          | ((X4) = (X3))
% 2.64/2.84          | ((X4) = (X0))
% 2.64/2.84          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.64/2.84      inference('cnf', [status(esa)], [d2_tarski])).
% 2.64/2.84  thf('2', plain,
% 2.64/2.84      (![X0 : $i, X3 : $i, X4 : $i]:
% 2.64/2.84         (((X4) = (X0))
% 2.64/2.84          | ((X4) = (X3))
% 2.64/2.84          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 2.64/2.84      inference('simplify', [status(thm)], ['1'])).
% 2.64/2.84  thf('3', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 2.64/2.84          | ((sk_B_1 @ (k2_tarski @ X1 @ X0)) = (X1))
% 2.64/2.84          | ((sk_B_1 @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 2.64/2.84      inference('sup-', [status(thm)], ['0', '2'])).
% 2.64/2.84  thf('4', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.64/2.84         (((X1) != (X0))
% 2.64/2.84          | (r2_hidden @ X1 @ X2)
% 2.64/2.84          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.64/2.84      inference('cnf', [status(esa)], [d2_tarski])).
% 2.64/2.84  thf('5', plain,
% 2.64/2.84      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 2.64/2.84      inference('simplify', [status(thm)], ['4'])).
% 2.64/2.84  thf(t51_mcart_1, conjecture,
% 2.64/2.84    (![A:$i,B:$i,C:$i]:
% 2.64/2.84     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84          ( ( C ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84          ( ~( ![D:$i]:
% 2.64/2.84               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.64/2.84                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 2.64/2.84                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 2.64/2.84                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 2.64/2.84  thf(zf_stmt_0, negated_conjecture,
% 2.64/2.84    (~( ![A:$i,B:$i,C:$i]:
% 2.64/2.84        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84             ( ( C ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84             ( ~( ![D:$i]:
% 2.64/2.84                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.64/2.84                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 2.64/2.84                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 2.64/2.84                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 2.64/2.84    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 2.64/2.84  thf('6', plain,
% 2.64/2.84      ((m1_subset_1 @ sk_D_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.64/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.84  thf(t50_mcart_1, axiom,
% 2.64/2.84    (![A:$i,B:$i,C:$i]:
% 2.64/2.84     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84          ( ( C ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84          ( ~( ![D:$i]:
% 2.64/2.84               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.64/2.84                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 2.64/2.84                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 2.64/2.84                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 2.64/2.84                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 2.64/2.84                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 2.64/2.84  thf('7', plain,
% 2.64/2.84      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 2.64/2.84         (((X52) = (k1_xboole_0))
% 2.64/2.84          | ((X53) = (k1_xboole_0))
% 2.64/2.84          | ((k6_mcart_1 @ X52 @ X53 @ X55 @ X54)
% 2.64/2.84              = (k2_mcart_1 @ (k1_mcart_1 @ X54)))
% 2.64/2.84          | ~ (m1_subset_1 @ X54 @ (k3_zfmisc_1 @ X52 @ X53 @ X55))
% 2.64/2.84          | ((X55) = (k1_xboole_0)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.64/2.84  thf('8', plain,
% 2.64/2.84      ((((sk_C_1) = (k1_xboole_0))
% 2.64/2.84        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)
% 2.64/2.84            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)))
% 2.64/2.84        | ((sk_B_2) = (k1_xboole_0))
% 2.64/2.84        | ((sk_A) = (k1_xboole_0)))),
% 2.64/2.84      inference('sup-', [status(thm)], ['6', '7'])).
% 2.64/2.84  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 2.64/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.84  thf('10', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.64/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.84  thf('11', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.64/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.84  thf('12', plain,
% 2.64/2.84      (((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)
% 2.64/2.84         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)))),
% 2.64/2.84      inference('simplify_reflect-', [status(thm)], ['8', '9', '10', '11'])).
% 2.64/2.84  thf('13', plain,
% 2.64/2.84      ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))
% 2.64/2.84        | ((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))
% 2.64/2.84        | ((sk_D_3) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))),
% 2.64/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.84  thf('14', plain,
% 2.64/2.84      ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))
% 2.64/2.84         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.84      inference('split', [status(esa)], ['13'])).
% 2.64/2.84  thf('15', plain,
% 2.64/2.84      ((((sk_D_3) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3))))
% 2.64/2.84         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.84      inference('sup+', [status(thm)], ['12', '14'])).
% 2.64/2.84  thf('16', plain,
% 2.64/2.84      ((m1_subset_1 @ sk_D_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.64/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.84  thf(l44_mcart_1, axiom,
% 2.64/2.84    (![A:$i,B:$i,C:$i]:
% 2.64/2.84     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84          ( ( C ) != ( k1_xboole_0 ) ) & 
% 2.64/2.84          ( ?[D:$i]:
% 2.64/2.84            ( ( ![E:$i]:
% 2.64/2.84                ( ( m1_subset_1 @ E @ A ) =>
% 2.64/2.84                  ( ![F:$i]:
% 2.64/2.84                    ( ( m1_subset_1 @ F @ B ) =>
% 2.64/2.84                      ( ![G:$i]:
% 2.64/2.84                        ( ( m1_subset_1 @ G @ C ) =>
% 2.64/2.84                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 2.64/2.84              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.64/2.84  thf('17', plain,
% 2.64/2.84      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.64/2.84         (((X43) = (k1_xboole_0))
% 2.64/2.84          | ((X44) = (k1_xboole_0))
% 2.64/2.84          | ((X45)
% 2.64/2.84              = (k3_mcart_1 @ (sk_E_2 @ X45 @ X46 @ X44 @ X43) @ 
% 2.64/2.84                 (sk_F_2 @ X45 @ X46 @ X44 @ X43) @ 
% 2.64/2.84                 (sk_G @ X45 @ X46 @ X44 @ X43)))
% 2.64/2.84          | ~ (m1_subset_1 @ X45 @ (k3_zfmisc_1 @ X43 @ X44 @ X46))
% 2.64/2.84          | ((X46) = (k1_xboole_0)))),
% 2.64/2.84      inference('cnf', [status(esa)], [l44_mcart_1])).
% 2.64/2.84  thf('18', plain,
% 2.64/2.84      ((((sk_C_1) = (k1_xboole_0))
% 2.64/2.84        | ((sk_D_3)
% 2.64/2.84            = (k3_mcart_1 @ (sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.84               (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.84               (sk_G @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A)))
% 2.64/2.85        | ((sk_B_2) = (k1_xboole_0))
% 2.64/2.85        | ((sk_A) = (k1_xboole_0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['16', '17'])).
% 2.64/2.85  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('20', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('21', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('22', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.85            (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.85            (sk_G @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A)))),
% 2.64/2.85      inference('simplify_reflect-', [status(thm)], ['18', '19', '20', '21'])).
% 2.64/2.85  thf('23', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.85            (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.85            (sk_G @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A)))),
% 2.64/2.85      inference('simplify_reflect-', [status(thm)], ['18', '19', '20', '21'])).
% 2.64/2.85  thf(d3_mcart_1, axiom,
% 2.64/2.85    (![A:$i,B:$i,C:$i]:
% 2.64/2.85     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 2.64/2.85  thf('24', plain,
% 2.64/2.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.64/2.85         ((k3_mcart_1 @ X37 @ X38 @ X39)
% 2.64/2.85           = (k4_tarski @ (k4_tarski @ X37 @ X38) @ X39))),
% 2.64/2.85      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.64/2.85  thf(t7_mcart_1, axiom,
% 2.64/2.85    (![A:$i,B:$i]:
% 2.64/2.85     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 2.64/2.85       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 2.64/2.85  thf('25', plain,
% 2.64/2.85      (![X56 : $i, X58 : $i]: ((k2_mcart_1 @ (k4_tarski @ X56 @ X58)) = (X58))),
% 2.64/2.85      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.64/2.85  thf('26', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 2.64/2.85      inference('sup+', [status(thm)], ['24', '25'])).
% 2.64/2.85  thf('27', plain,
% 2.64/2.85      (((k2_mcart_1 @ sk_D_3) = (sk_G @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 2.64/2.85      inference('sup+', [status(thm)], ['23', '26'])).
% 2.64/2.85  thf('28', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.85            (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ (k2_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('demod', [status(thm)], ['22', '27'])).
% 2.64/2.85  thf('29', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.85            (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ (k2_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('demod', [status(thm)], ['22', '27'])).
% 2.64/2.85  thf('30', plain,
% 2.64/2.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.64/2.85         ((k3_mcart_1 @ X37 @ X38 @ X39)
% 2.64/2.85           = (k4_tarski @ (k4_tarski @ X37 @ X38) @ X39))),
% 2.64/2.85      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.64/2.85  thf('31', plain,
% 2.64/2.85      (![X56 : $i, X57 : $i]: ((k1_mcart_1 @ (k4_tarski @ X56 @ X57)) = (X56))),
% 2.64/2.85      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.64/2.85  thf('32', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 2.64/2.85      inference('sup+', [status(thm)], ['30', '31'])).
% 2.64/2.85  thf('33', plain,
% 2.64/2.85      (![X56 : $i, X57 : $i]: ((k1_mcart_1 @ (k4_tarski @ X56 @ X57)) = (X56))),
% 2.64/2.85      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.64/2.85  thf('34', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((k1_mcart_1 @ (k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0))) = (X2))),
% 2.64/2.85      inference('sup+', [status(thm)], ['32', '33'])).
% 2.64/2.85  thf('35', plain,
% 2.64/2.85      (((k1_mcart_1 @ (k1_mcart_1 @ sk_D_3))
% 2.64/2.85         = (sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 2.64/2.85      inference('sup+', [status(thm)], ['29', '34'])).
% 2.64/2.85  thf('36', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ 
% 2.64/2.85            (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ (k2_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('demod', [status(thm)], ['28', '35'])).
% 2.64/2.85  thf('37', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ 
% 2.64/2.85            (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ (k2_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('demod', [status(thm)], ['28', '35'])).
% 2.64/2.85  thf('38', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 2.64/2.85      inference('sup+', [status(thm)], ['30', '31'])).
% 2.64/2.85  thf('39', plain,
% 2.64/2.85      (![X56 : $i, X58 : $i]: ((k2_mcart_1 @ (k4_tarski @ X56 @ X58)) = (X58))),
% 2.64/2.85      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.64/2.85  thf('40', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((k2_mcart_1 @ (k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0))) = (X1))),
% 2.64/2.85      inference('sup+', [status(thm)], ['38', '39'])).
% 2.64/2.85  thf('41', plain,
% 2.64/2.85      (((k2_mcart_1 @ (k1_mcart_1 @ sk_D_3))
% 2.64/2.85         = (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 2.64/2.85      inference('sup+', [status(thm)], ['37', '40'])).
% 2.64/2.85  thf('42', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ 
% 2.64/2.85            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ (k2_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('demod', [status(thm)], ['36', '41'])).
% 2.64/2.85  thf('43', plain,
% 2.64/2.85      ((((sk_D_3)
% 2.64/2.85          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ sk_D_3 @ 
% 2.64/2.85             (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['15', '42'])).
% 2.64/2.85  thf('44', plain,
% 2.64/2.85      ((((sk_D_3)
% 2.64/2.85          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ sk_D_3 @ 
% 2.64/2.85             (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['15', '42'])).
% 2.64/2.85  thf('45', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 2.64/2.85      inference('sup+', [status(thm)], ['30', '31'])).
% 2.64/2.85  thf('46', plain,
% 2.64/2.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.64/2.85         ((k3_mcart_1 @ X37 @ X38 @ X39)
% 2.64/2.85           = (k4_tarski @ (k4_tarski @ X37 @ X38) @ X39))),
% 2.64/2.85      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.64/2.85  thf('47', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.64/2.85         ((k3_mcart_1 @ X2 @ X1 @ X3)
% 2.64/2.85           = (k4_tarski @ (k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) @ X3))),
% 2.64/2.85      inference('sup+', [status(thm)], ['45', '46'])).
% 2.64/2.85  thf('48', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ sk_D_3 @ X0)
% 2.64/2.85            = (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ X0)))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['44', '47'])).
% 2.64/2.85  thf('49', plain,
% 2.64/2.85      ((((sk_D_3) = (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('demod', [status(thm)], ['43', '48'])).
% 2.64/2.85  thf('50', plain,
% 2.64/2.85      (![X59 : $i, X60 : $i, X61 : $i]:
% 2.64/2.85         (((X59) = (k1_xboole_0))
% 2.64/2.85          | ~ (r2_hidden @ X61 @ X59)
% 2.64/2.85          | ((sk_B_1 @ X59) != (k4_tarski @ X61 @ X60)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.64/2.85  thf('51', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (((sk_B_1 @ X0) != (sk_D_3))
% 2.64/2.85           | ~ (r2_hidden @ (k1_mcart_1 @ sk_D_3) @ X0)
% 2.64/2.85           | ((X0) = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['49', '50'])).
% 2.64/2.85  thf('52', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (((k2_tarski @ X0 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85           | ((sk_B_1 @ (k2_tarski @ X0 @ (k1_mcart_1 @ sk_D_3))) != (sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['5', '51'])).
% 2.64/2.85  thf('53', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (((X0) != (sk_D_3))
% 2.64/2.85           | ((sk_B_1 @ (k2_tarski @ X0 @ (k1_mcart_1 @ sk_D_3)))
% 2.64/2.85               = (k1_mcart_1 @ sk_D_3))
% 2.64/2.85           | ((k2_tarski @ X0 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85           | ((k2_tarski @ X0 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['3', '52'])).
% 2.64/2.85  thf('54', plain,
% 2.64/2.85      (((((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85         | ((sk_B_1 @ (k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)))
% 2.64/2.85             = (k1_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('simplify', [status(thm)], ['53'])).
% 2.64/2.85  thf('55', plain,
% 2.64/2.85      ((((sk_D_3) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['12', '14'])).
% 2.64/2.85  thf('56', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ 
% 2.64/2.85            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ (k2_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('demod', [status(thm)], ['36', '41'])).
% 2.64/2.85  thf('57', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 2.64/2.85      inference('sup+', [status(thm)], ['30', '31'])).
% 2.64/2.85  thf('58', plain,
% 2.64/2.85      (![X59 : $i, X60 : $i, X61 : $i]:
% 2.64/2.85         (((X59) = (k1_xboole_0))
% 2.64/2.85          | ~ (r2_hidden @ X60 @ X59)
% 2.64/2.85          | ((sk_B_1 @ X59) != (k4_tarski @ X61 @ X60)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.64/2.85  thf('59', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.64/2.85         (((sk_B_1 @ X3) != (k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 2.64/2.85          | ~ (r2_hidden @ X1 @ X3)
% 2.64/2.85          | ((X3) = (k1_xboole_0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['57', '58'])).
% 2.64/2.85  thf('60', plain,
% 2.64/2.85      (![X0 : $i]:
% 2.64/2.85         (((sk_B_1 @ X0) != (k1_mcart_1 @ sk_D_3))
% 2.64/2.85          | ((X0) = (k1_xboole_0))
% 2.64/2.85          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ X0))),
% 2.64/2.85      inference('sup-', [status(thm)], ['56', '59'])).
% 2.64/2.85  thf('61', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (~ (r2_hidden @ sk_D_3 @ X0)
% 2.64/2.85           | ((X0) = (k1_xboole_0))
% 2.64/2.85           | ((sk_B_1 @ X0) != (k1_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['55', '60'])).
% 2.64/2.85  thf('62', plain,
% 2.64/2.85      (((((k1_mcart_1 @ sk_D_3) != (k1_mcart_1 @ sk_D_3))
% 2.64/2.85         | ((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85         | ((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85         | ~ (r2_hidden @ sk_D_3 @ (k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['54', '61'])).
% 2.64/2.85  thf('63', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.64/2.85         (((X1) != (X3))
% 2.64/2.85          | (r2_hidden @ X1 @ X2)
% 2.64/2.85          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.64/2.85      inference('cnf', [status(esa)], [d2_tarski])).
% 2.64/2.85  thf('64', plain,
% 2.64/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 2.64/2.85      inference('simplify', [status(thm)], ['63'])).
% 2.64/2.85  thf('65', plain,
% 2.64/2.85      (((((k1_mcart_1 @ sk_D_3) != (k1_mcart_1 @ sk_D_3))
% 2.64/2.85         | ((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85         | ((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('demod', [status(thm)], ['62', '64'])).
% 2.64/2.85  thf('66', plain,
% 2.64/2.85      ((((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0)))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('simplify', [status(thm)], ['65'])).
% 2.64/2.85  thf('67', plain,
% 2.64/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 2.64/2.85      inference('simplify', [status(thm)], ['63'])).
% 2.64/2.85  thf('68', plain,
% 2.64/2.85      (((r2_hidden @ sk_D_3 @ k1_xboole_0))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['66', '67'])).
% 2.64/2.85  thf('69', plain,
% 2.64/2.85      ((m1_subset_1 @ sk_D_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('70', plain,
% 2.64/2.85      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 2.64/2.85         (((X52) = (k1_xboole_0))
% 2.64/2.85          | ((X53) = (k1_xboole_0))
% 2.64/2.85          | ((k7_mcart_1 @ X52 @ X53 @ X55 @ X54) = (k2_mcart_1 @ X54))
% 2.64/2.85          | ~ (m1_subset_1 @ X54 @ (k3_zfmisc_1 @ X52 @ X53 @ X55))
% 2.64/2.85          | ((X55) = (k1_xboole_0)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.64/2.85  thf('71', plain,
% 2.64/2.85      ((((sk_C_1) = (k1_xboole_0))
% 2.64/2.85        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)
% 2.64/2.85            = (k2_mcart_1 @ sk_D_3))
% 2.64/2.85        | ((sk_B_2) = (k1_xboole_0))
% 2.64/2.85        | ((sk_A) = (k1_xboole_0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['69', '70'])).
% 2.64/2.85  thf('72', plain, (((sk_A) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('73', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('74', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('75', plain,
% 2.64/2.85      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3) = (k2_mcart_1 @ sk_D_3))),
% 2.64/2.85      inference('simplify_reflect-', [status(thm)], ['71', '72', '73', '74'])).
% 2.64/2.85  thf('76', plain,
% 2.64/2.85      ((((sk_D_3) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))
% 2.64/2.85         <= ((((sk_D_3) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('split', [status(esa)], ['13'])).
% 2.64/2.85  thf('77', plain,
% 2.64/2.85      ((((sk_D_3) = (k2_mcart_1 @ sk_D_3)))
% 2.64/2.85         <= ((((sk_D_3) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['75', '76'])).
% 2.64/2.85  thf('78', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.85            (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ (k2_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('demod', [status(thm)], ['22', '27'])).
% 2.64/2.85  thf('79', plain,
% 2.64/2.85      ((((sk_D_3)
% 2.64/2.85          = (k3_mcart_1 @ (sk_E_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 2.64/2.85             (sk_F_2 @ sk_D_3 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_D_3)))
% 2.64/2.85         <= ((((sk_D_3) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['77', '78'])).
% 2.64/2.85  thf('80', plain,
% 2.64/2.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.64/2.85         ((k3_mcart_1 @ X37 @ X38 @ X39)
% 2.64/2.85           = (k4_tarski @ (k4_tarski @ X37 @ X38) @ X39))),
% 2.64/2.85      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.64/2.85  thf(t20_mcart_1, axiom,
% 2.64/2.85    (![A:$i]:
% 2.64/2.85     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 2.64/2.85       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 2.64/2.85  thf('81', plain,
% 2.64/2.85      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.64/2.85         (((X47) != (k2_mcart_1 @ X47)) | ((X47) != (k4_tarski @ X48 @ X49)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t20_mcart_1])).
% 2.64/2.85  thf('82', plain,
% 2.64/2.85      (![X48 : $i, X49 : $i]:
% 2.64/2.85         ((k4_tarski @ X48 @ X49) != (k2_mcart_1 @ (k4_tarski @ X48 @ X49)))),
% 2.64/2.85      inference('simplify', [status(thm)], ['81'])).
% 2.64/2.85  thf('83', plain,
% 2.64/2.85      (![X56 : $i, X58 : $i]: ((k2_mcart_1 @ (k4_tarski @ X56 @ X58)) = (X58))),
% 2.64/2.85      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.64/2.85  thf('84', plain, (![X48 : $i, X49 : $i]: ((k4_tarski @ X48 @ X49) != (X49))),
% 2.64/2.85      inference('demod', [status(thm)], ['82', '83'])).
% 2.64/2.85  thf('85', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 2.64/2.85      inference('sup-', [status(thm)], ['80', '84'])).
% 2.64/2.85  thf('86', plain,
% 2.64/2.85      (~ (((sk_D_3) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))),
% 2.64/2.85      inference('simplify_reflect-', [status(thm)], ['79', '85'])).
% 2.64/2.85  thf('87', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i]:
% 2.64/2.85         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 2.64/2.85          | ((sk_B_1 @ (k2_tarski @ X1 @ X0)) = (X1))
% 2.64/2.85          | ((sk_B_1 @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['0', '2'])).
% 2.64/2.85  thf('88', plain,
% 2.64/2.85      ((m1_subset_1 @ sk_D_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('89', plain,
% 2.64/2.85      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 2.64/2.85         (((X52) = (k1_xboole_0))
% 2.64/2.85          | ((X53) = (k1_xboole_0))
% 2.64/2.85          | ((k5_mcart_1 @ X52 @ X53 @ X55 @ X54)
% 2.64/2.85              = (k1_mcart_1 @ (k1_mcart_1 @ X54)))
% 2.64/2.85          | ~ (m1_subset_1 @ X54 @ (k3_zfmisc_1 @ X52 @ X53 @ X55))
% 2.64/2.85          | ((X55) = (k1_xboole_0)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.64/2.85  thf('90', plain,
% 2.64/2.85      ((((sk_C_1) = (k1_xboole_0))
% 2.64/2.85        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)
% 2.64/2.85            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)))
% 2.64/2.85        | ((sk_B_2) = (k1_xboole_0))
% 2.64/2.85        | ((sk_A) = (k1_xboole_0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['88', '89'])).
% 2.64/2.85  thf('91', plain, (((sk_A) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('92', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('93', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.85  thf('94', plain,
% 2.64/2.85      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)
% 2.64/2.85         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('simplify_reflect-', [status(thm)], ['90', '91', '92', '93'])).
% 2.64/2.85  thf('95', plain,
% 2.64/2.85      ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('split', [status(esa)], ['13'])).
% 2.64/2.85  thf('96', plain,
% 2.64/2.85      ((((sk_D_3) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['94', '95'])).
% 2.64/2.85  thf('97', plain,
% 2.64/2.85      (((sk_D_3)
% 2.64/2.85         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ 
% 2.64/2.85            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ (k2_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('demod', [status(thm)], ['36', '41'])).
% 2.64/2.85  thf('98', plain,
% 2.64/2.85      ((((sk_D_3)
% 2.64/2.85          = (k3_mcart_1 @ sk_D_3 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ 
% 2.64/2.85             (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['96', '97'])).
% 2.64/2.85  thf('99', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 2.64/2.85      inference('sup+', [status(thm)], ['30', '31'])).
% 2.64/2.85  thf('100', plain,
% 2.64/2.85      ((((k1_mcart_1 @ sk_D_3)
% 2.64/2.85          = (k4_tarski @ sk_D_3 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['98', '99'])).
% 2.64/2.85  thf('101', plain,
% 2.64/2.85      ((((sk_D_3)
% 2.64/2.85          = (k3_mcart_1 @ sk_D_3 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ 
% 2.64/2.85             (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['96', '97'])).
% 2.64/2.85  thf('102', plain,
% 2.64/2.85      ((((k1_mcart_1 @ sk_D_3)
% 2.64/2.85          = (k4_tarski @ sk_D_3 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['98', '99'])).
% 2.64/2.85  thf('103', plain,
% 2.64/2.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.64/2.85         ((k3_mcart_1 @ X37 @ X38 @ X39)
% 2.64/2.85           = (k4_tarski @ (k4_tarski @ X37 @ X38) @ X39))),
% 2.64/2.85      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.64/2.85  thf('104', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          ((k3_mcart_1 @ sk_D_3 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_3)) @ X0)
% 2.64/2.85            = (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ X0)))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['102', '103'])).
% 2.64/2.85  thf('105', plain,
% 2.64/2.85      ((((sk_D_3) = (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('demod', [status(thm)], ['101', '104'])).
% 2.64/2.85  thf('106', plain,
% 2.64/2.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.64/2.85         ((k3_mcart_1 @ X37 @ X38 @ X39)
% 2.64/2.85           = (k4_tarski @ (k4_tarski @ X37 @ X38) @ X39))),
% 2.64/2.85      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.64/2.85  thf('107', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          ((k3_mcart_1 @ (k1_mcart_1 @ sk_D_3) @ (k2_mcart_1 @ sk_D_3) @ X0)
% 2.64/2.85            = (k4_tarski @ sk_D_3 @ X0)))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['105', '106'])).
% 2.64/2.85  thf('108', plain,
% 2.64/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 2.64/2.85      inference('simplify', [status(thm)], ['63'])).
% 2.64/2.85  thf('109', plain,
% 2.64/2.85      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.64/2.85         ((k3_mcart_1 @ X37 @ X38 @ X39)
% 2.64/2.85           = (k4_tarski @ (k4_tarski @ X37 @ X38) @ X39))),
% 2.64/2.85      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.64/2.85  thf('110', plain,
% 2.64/2.85      (![X59 : $i, X60 : $i, X61 : $i]:
% 2.64/2.85         (((X59) = (k1_xboole_0))
% 2.64/2.85          | ~ (r2_hidden @ X61 @ X59)
% 2.64/2.85          | ((sk_B_1 @ X59) != (k4_tarski @ X61 @ X60)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.64/2.85  thf('111', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.64/2.85         (((sk_B_1 @ X3) != (k3_mcart_1 @ X2 @ X1 @ X0))
% 2.64/2.85          | ~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ X3)
% 2.64/2.85          | ((X3) = (k1_xboole_0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['109', '110'])).
% 2.64/2.85  thf('112', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.64/2.85         (((k2_tarski @ (k4_tarski @ X2 @ X1) @ X0) = (k1_xboole_0))
% 2.64/2.85          | ((sk_B_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X0))
% 2.64/2.85              != (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['108', '111'])).
% 2.64/2.85  thf('113', plain,
% 2.64/2.85      ((![X0 : $i, X1 : $i]:
% 2.64/2.85          (((sk_B_1 @ 
% 2.64/2.85             (k2_tarski @ 
% 2.64/2.85              (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ (k2_mcart_1 @ sk_D_3)) @ X1))
% 2.64/2.85             != (k4_tarski @ sk_D_3 @ X0))
% 2.64/2.85           | ((k2_tarski @ 
% 2.64/2.85               (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ (k2_mcart_1 @ sk_D_3)) @ X1)
% 2.64/2.85               = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['107', '112'])).
% 2.64/2.85  thf('114', plain,
% 2.64/2.85      ((((sk_D_3) = (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('demod', [status(thm)], ['101', '104'])).
% 2.64/2.85  thf('115', plain,
% 2.64/2.85      ((((sk_D_3) = (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('demod', [status(thm)], ['101', '104'])).
% 2.64/2.85  thf('116', plain,
% 2.64/2.85      ((![X0 : $i, X1 : $i]:
% 2.64/2.85          (((sk_B_1 @ (k2_tarski @ sk_D_3 @ X1)) != (k4_tarski @ sk_D_3 @ X0))
% 2.64/2.85           | ((k2_tarski @ sk_D_3 @ X1) = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('demod', [status(thm)], ['113', '114', '115'])).
% 2.64/2.85  thf('117', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (((sk_B_1 @ (k2_tarski @ sk_D_3 @ X0)) != (k1_mcart_1 @ sk_D_3))
% 2.64/2.85           | ((k2_tarski @ sk_D_3 @ X0) = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['100', '116'])).
% 2.64/2.85  thf('118', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (((X0) != (k1_mcart_1 @ sk_D_3))
% 2.64/2.85           | ((sk_B_1 @ (k2_tarski @ sk_D_3 @ X0)) = (sk_D_3))
% 2.64/2.85           | ((k2_tarski @ sk_D_3 @ X0) = (k1_xboole_0))
% 2.64/2.85           | ((k2_tarski @ sk_D_3 @ X0) = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['87', '117'])).
% 2.64/2.85  thf('119', plain,
% 2.64/2.85      (((((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85         | ((sk_B_1 @ (k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3))) = (sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('simplify', [status(thm)], ['118'])).
% 2.64/2.85  thf('120', plain,
% 2.64/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 2.64/2.85      inference('simplify', [status(thm)], ['4'])).
% 2.64/2.85  thf('121', plain,
% 2.64/2.85      ((((sk_D_3) = (k4_tarski @ (k1_mcart_1 @ sk_D_3) @ (k2_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('demod', [status(thm)], ['101', '104'])).
% 2.64/2.85  thf('122', plain,
% 2.64/2.85      (![X59 : $i, X60 : $i, X61 : $i]:
% 2.64/2.85         (((X59) = (k1_xboole_0))
% 2.64/2.85          | ~ (r2_hidden @ X61 @ X59)
% 2.64/2.85          | ((sk_B_1 @ X59) != (k4_tarski @ X61 @ X60)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t9_mcart_1])).
% 2.64/2.85  thf('123', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (((sk_B_1 @ X0) != (sk_D_3))
% 2.64/2.85           | ~ (r2_hidden @ (k1_mcart_1 @ sk_D_3) @ X0)
% 2.64/2.85           | ((X0) = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['121', '122'])).
% 2.64/2.85  thf('124', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (((k2_tarski @ X0 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85           | ((sk_B_1 @ (k2_tarski @ X0 @ (k1_mcart_1 @ sk_D_3))) != (sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['120', '123'])).
% 2.64/2.85  thf('125', plain,
% 2.64/2.85      (((((sk_D_3) != (sk_D_3))
% 2.64/2.85         | ((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))
% 2.64/2.85         | ((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['119', '124'])).
% 2.64/2.85  thf('126', plain,
% 2.64/2.85      ((((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0)))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('simplify', [status(thm)], ['125'])).
% 2.64/2.85  thf('127', plain,
% 2.64/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 2.64/2.85      inference('simplify', [status(thm)], ['63'])).
% 2.64/2.85  thf('128', plain,
% 2.64/2.85      (((r2_hidden @ sk_D_3 @ k1_xboole_0))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup+', [status(thm)], ['126', '127'])).
% 2.64/2.85  thf('129', plain,
% 2.64/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 2.64/2.85      inference('simplify', [status(thm)], ['4'])).
% 2.64/2.85  thf(t72_zfmisc_1, axiom,
% 2.64/2.85    (![A:$i,B:$i,C:$i]:
% 2.64/2.85     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.64/2.85       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 2.64/2.85  thf('130', plain,
% 2.64/2.85      (![X28 : $i, X30 : $i, X31 : $i]:
% 2.64/2.85         (((k4_xboole_0 @ (k2_tarski @ X28 @ X30) @ X31)
% 2.64/2.85            = (k2_tarski @ X28 @ X30))
% 2.64/2.85          | (r2_hidden @ X30 @ X31)
% 2.64/2.85          | (r2_hidden @ X28 @ X31))),
% 2.64/2.85      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 2.64/2.85  thf(t65_zfmisc_1, axiom,
% 2.64/2.85    (![A:$i,B:$i]:
% 2.64/2.85     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.64/2.85       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.64/2.85  thf('131', plain,
% 2.64/2.85      (![X25 : $i, X26 : $i]:
% 2.64/2.85         (~ (r2_hidden @ X25 @ X26)
% 2.64/2.85          | ((k4_xboole_0 @ X26 @ (k1_tarski @ X25)) != (X26)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.64/2.85  thf('132', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 2.64/2.85          | (r2_hidden @ X1 @ (k1_tarski @ X2))
% 2.64/2.85          | (r2_hidden @ X0 @ (k1_tarski @ X2))
% 2.64/2.85          | ~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['130', '131'])).
% 2.64/2.85  thf('133', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.64/2.85          | (r2_hidden @ X0 @ (k1_tarski @ X2))
% 2.64/2.85          | (r2_hidden @ X1 @ (k1_tarski @ X2)))),
% 2.64/2.85      inference('simplify', [status(thm)], ['132'])).
% 2.64/2.85  thf('134', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i]:
% 2.64/2.85         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.64/2.85          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['129', '133'])).
% 2.64/2.85  thf('135', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.64/2.85      inference('condensation', [status(thm)], ['134'])).
% 2.64/2.85  thf(d2_zfmisc_1, axiom,
% 2.64/2.85    (![A:$i,B:$i,C:$i]:
% 2.64/2.85     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.64/2.85       ( ![D:$i]:
% 2.64/2.85         ( ( r2_hidden @ D @ C ) <=>
% 2.64/2.85           ( ?[E:$i,F:$i]:
% 2.64/2.85             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 2.64/2.85               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 2.64/2.85  thf(zf_stmt_1, axiom,
% 2.64/2.85    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 2.64/2.85     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 2.64/2.85       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 2.64/2.85         ( r2_hidden @ E @ A ) ) ))).
% 2.64/2.85  thf('136', plain,
% 2.64/2.85      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 2.64/2.85         ((zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11)
% 2.64/2.85          | ~ (r2_hidden @ X6 @ X11)
% 2.64/2.85          | ~ (r2_hidden @ X7 @ X9)
% 2.64/2.85          | ((X8) != (k4_tarski @ X6 @ X7)))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.64/2.85  thf('137', plain,
% 2.64/2.85      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i]:
% 2.64/2.85         (~ (r2_hidden @ X7 @ X9)
% 2.64/2.85          | ~ (r2_hidden @ X6 @ X11)
% 2.64/2.85          | (zip_tseitin_0 @ X7 @ X6 @ (k4_tarski @ X6 @ X7) @ X9 @ X11))),
% 2.64/2.85      inference('simplify', [status(thm)], ['136'])).
% 2.64/2.85  thf('138', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((zip_tseitin_0 @ X0 @ X2 @ (k4_tarski @ X2 @ X0) @ 
% 2.64/2.85           (k1_tarski @ X0) @ X1)
% 2.64/2.85          | ~ (r2_hidden @ X2 @ X1))),
% 2.64/2.85      inference('sup-', [status(thm)], ['135', '137'])).
% 2.64/2.85  thf('139', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (zip_tseitin_0 @ X0 @ sk_D_3 @ (k4_tarski @ sk_D_3 @ X0) @ 
% 2.64/2.85           (k1_tarski @ X0) @ k1_xboole_0))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['128', '138'])).
% 2.64/2.85  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 2.64/2.85  thf(zf_stmt_3, axiom,
% 2.64/2.85    (![A:$i,B:$i,C:$i]:
% 2.64/2.85     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.64/2.85       ( ![D:$i]:
% 2.64/2.85         ( ( r2_hidden @ D @ C ) <=>
% 2.64/2.85           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 2.64/2.85  thf('140', plain,
% 2.64/2.85      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.85         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 2.64/2.85          | (r2_hidden @ X14 @ X17)
% 2.64/2.85          | ((X17) != (k2_zfmisc_1 @ X16 @ X15)))),
% 2.64/2.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.64/2.85  thf('141', plain,
% 2.64/2.85      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.64/2.85         ((r2_hidden @ X14 @ (k2_zfmisc_1 @ X16 @ X15))
% 2.64/2.85          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 2.64/2.85      inference('simplify', [status(thm)], ['140'])).
% 2.64/2.85  thf('142', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (r2_hidden @ (k4_tarski @ sk_D_3 @ X0) @ 
% 2.64/2.85           (k2_zfmisc_1 @ k1_xboole_0 @ (k1_tarski @ X0))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['139', '141'])).
% 2.64/2.85  thf(t113_zfmisc_1, axiom,
% 2.64/2.85    (![A:$i,B:$i]:
% 2.64/2.85     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.64/2.85       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.64/2.85  thf('143', plain,
% 2.64/2.85      (![X23 : $i, X24 : $i]:
% 2.64/2.85         (((k2_zfmisc_1 @ X23 @ X24) = (k1_xboole_0))
% 2.64/2.85          | ((X23) != (k1_xboole_0)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.64/2.85  thf('144', plain,
% 2.64/2.85      (![X24 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X24) = (k1_xboole_0))),
% 2.64/2.85      inference('simplify', [status(thm)], ['143'])).
% 2.64/2.85  thf('145', plain,
% 2.64/2.85      ((![X0 : $i]: (r2_hidden @ (k4_tarski @ sk_D_3 @ X0) @ k1_xboole_0))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('demod', [status(thm)], ['142', '144'])).
% 2.64/2.85  thf('146', plain,
% 2.64/2.85      ((((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0)))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('simplify', [status(thm)], ['125'])).
% 2.64/2.85  thf('147', plain,
% 2.64/2.85      (![X0 : $i, X3 : $i, X4 : $i]:
% 2.64/2.85         (((X4) = (X0))
% 2.64/2.85          | ((X4) = (X3))
% 2.64/2.85          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 2.64/2.85      inference('simplify', [status(thm)], ['1'])).
% 2.64/2.85  thf('148', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 2.64/2.85           | ((X0) = (sk_D_3))
% 2.64/2.85           | ((X0) = (k1_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['146', '147'])).
% 2.64/2.85  thf('149', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (((k4_tarski @ sk_D_3 @ X0) = (k1_mcart_1 @ sk_D_3))
% 2.64/2.85           | ((k4_tarski @ sk_D_3 @ X0) = (sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['145', '148'])).
% 2.64/2.85  thf('150', plain,
% 2.64/2.85      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.64/2.85         (((X47) != (k1_mcart_1 @ X47)) | ((X47) != (k4_tarski @ X48 @ X49)))),
% 2.64/2.85      inference('cnf', [status(esa)], [t20_mcart_1])).
% 2.64/2.85  thf('151', plain,
% 2.64/2.85      (![X48 : $i, X49 : $i]:
% 2.64/2.85         ((k4_tarski @ X48 @ X49) != (k1_mcart_1 @ (k4_tarski @ X48 @ X49)))),
% 2.64/2.85      inference('simplify', [status(thm)], ['150'])).
% 2.64/2.85  thf('152', plain,
% 2.64/2.85      (![X56 : $i, X57 : $i]: ((k1_mcart_1 @ (k4_tarski @ X56 @ X57)) = (X56))),
% 2.64/2.85      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.64/2.85  thf('153', plain,
% 2.64/2.85      (![X48 : $i, X49 : $i]: ((k4_tarski @ X48 @ X49) != (X48))),
% 2.64/2.85      inference('demod', [status(thm)], ['151', '152'])).
% 2.64/2.85  thf('154', plain,
% 2.64/2.85      ((![X0 : $i]: ((k4_tarski @ sk_D_3 @ X0) = (k1_mcart_1 @ sk_D_3)))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('simplify_reflect-', [status(thm)], ['149', '153'])).
% 2.64/2.85  thf('155', plain,
% 2.64/2.85      (![X48 : $i, X49 : $i]: ((k4_tarski @ X48 @ X49) != (X49))),
% 2.64/2.85      inference('demod', [status(thm)], ['82', '83'])).
% 2.64/2.85  thf('156', plain,
% 2.64/2.85      ((![X0 : $i]: ((k1_mcart_1 @ sk_D_3) != (X0)))
% 2.64/2.85         <= ((((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['154', '155'])).
% 2.64/2.85  thf('157', plain,
% 2.64/2.85      (~ (((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))),
% 2.64/2.85      inference('simplify', [status(thm)], ['156'])).
% 2.64/2.85  thf('158', plain,
% 2.64/2.85      ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))) | 
% 2.64/2.85       (((sk_D_3) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))) | 
% 2.64/2.85       (((sk_D_3) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))),
% 2.64/2.85      inference('split', [status(esa)], ['13'])).
% 2.64/2.85  thf('159', plain,
% 2.64/2.85      ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))),
% 2.64/2.85      inference('sat_resolution*', [status(thm)], ['86', '157', '158'])).
% 2.64/2.85  thf('160', plain, ((r2_hidden @ sk_D_3 @ k1_xboole_0)),
% 2.64/2.85      inference('simpl_trail', [status(thm)], ['68', '159'])).
% 2.64/2.85  thf('161', plain,
% 2.64/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.85         ((zip_tseitin_0 @ X0 @ X2 @ (k4_tarski @ X2 @ X0) @ 
% 2.64/2.85           (k1_tarski @ X0) @ X1)
% 2.64/2.85          | ~ (r2_hidden @ X2 @ X1))),
% 2.64/2.85      inference('sup-', [status(thm)], ['135', '137'])).
% 2.64/2.85  thf('162', plain,
% 2.64/2.85      (![X0 : $i]:
% 2.64/2.85         (zip_tseitin_0 @ X0 @ sk_D_3 @ (k4_tarski @ sk_D_3 @ X0) @ 
% 2.64/2.85          (k1_tarski @ X0) @ k1_xboole_0)),
% 2.64/2.85      inference('sup-', [status(thm)], ['160', '161'])).
% 2.64/2.85  thf('163', plain,
% 2.64/2.85      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.64/2.85         ((r2_hidden @ X14 @ (k2_zfmisc_1 @ X16 @ X15))
% 2.64/2.85          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 2.64/2.85      inference('simplify', [status(thm)], ['140'])).
% 2.64/2.85  thf('164', plain,
% 2.64/2.85      (![X0 : $i]:
% 2.64/2.85         (r2_hidden @ (k4_tarski @ sk_D_3 @ X0) @ 
% 2.64/2.85          (k2_zfmisc_1 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['162', '163'])).
% 2.64/2.85  thf('165', plain,
% 2.64/2.85      (![X24 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X24) = (k1_xboole_0))),
% 2.64/2.85      inference('simplify', [status(thm)], ['143'])).
% 2.64/2.85  thf('166', plain,
% 2.64/2.85      (![X0 : $i]: (r2_hidden @ (k4_tarski @ sk_D_3 @ X0) @ k1_xboole_0)),
% 2.64/2.85      inference('demod', [status(thm)], ['164', '165'])).
% 2.64/2.85  thf('167', plain,
% 2.64/2.85      ((((k2_tarski @ sk_D_3 @ (k1_mcart_1 @ sk_D_3)) = (k1_xboole_0)))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('simplify', [status(thm)], ['65'])).
% 2.64/2.85  thf('168', plain,
% 2.64/2.85      (![X0 : $i, X3 : $i, X4 : $i]:
% 2.64/2.85         (((X4) = (X0))
% 2.64/2.85          | ((X4) = (X3))
% 2.64/2.85          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 2.64/2.85      inference('simplify', [status(thm)], ['1'])).
% 2.64/2.85  thf('169', plain,
% 2.64/2.85      ((![X0 : $i]:
% 2.64/2.85          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 2.64/2.85           | ((X0) = (sk_D_3))
% 2.64/2.85           | ((X0) = (k1_mcart_1 @ sk_D_3))))
% 2.64/2.85         <= ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3))))),
% 2.64/2.85      inference('sup-', [status(thm)], ['167', '168'])).
% 2.64/2.85  thf('170', plain,
% 2.64/2.85      ((((sk_D_3) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D_3)))),
% 2.64/2.85      inference('sat_resolution*', [status(thm)], ['86', '157', '158'])).
% 2.64/2.85  thf('171', plain,
% 2.64/2.85      (![X0 : $i]:
% 2.64/2.85         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 2.64/2.85          | ((X0) = (sk_D_3))
% 2.64/2.85          | ((X0) = (k1_mcart_1 @ sk_D_3)))),
% 2.64/2.85      inference('simpl_trail', [status(thm)], ['169', '170'])).
% 2.64/2.85  thf('172', plain,
% 2.64/2.85      (![X0 : $i]:
% 2.64/2.85         (((k4_tarski @ sk_D_3 @ X0) = (k1_mcart_1 @ sk_D_3))
% 2.64/2.85          | ((k4_tarski @ sk_D_3 @ X0) = (sk_D_3)))),
% 2.64/2.85      inference('sup-', [status(thm)], ['166', '171'])).
% 2.64/2.85  thf('173', plain,
% 2.64/2.85      (![X48 : $i, X49 : $i]: ((k4_tarski @ X48 @ X49) != (X48))),
% 2.64/2.85      inference('demod', [status(thm)], ['151', '152'])).
% 2.64/2.85  thf('174', plain,
% 2.64/2.85      (![X0 : $i]: ((k4_tarski @ sk_D_3 @ X0) = (k1_mcart_1 @ sk_D_3))),
% 2.64/2.85      inference('simplify_reflect-', [status(thm)], ['172', '173'])).
% 2.64/2.85  thf('175', plain,
% 2.64/2.85      (![X48 : $i, X49 : $i]: ((k4_tarski @ X48 @ X49) != (X49))),
% 2.64/2.85      inference('demod', [status(thm)], ['82', '83'])).
% 2.64/2.85  thf('176', plain, (![X0 : $i]: ((k1_mcart_1 @ sk_D_3) != (X0))),
% 2.64/2.85      inference('sup-', [status(thm)], ['174', '175'])).
% 2.64/2.85  thf('177', plain, ($false), inference('simplify', [status(thm)], ['176'])).
% 2.64/2.85  
% 2.64/2.85  % SZS output end Refutation
% 2.64/2.85  
% 2.64/2.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
