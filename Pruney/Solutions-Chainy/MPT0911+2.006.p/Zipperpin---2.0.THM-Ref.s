%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Scq9loWCZ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:56 EST 2020

% Result     : Theorem 8.53s
% Output     : Refutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :  310 (16490 expanded)
%              Number of leaves         :   45 (5024 expanded)
%              Depth                    :   44
%              Number of atoms          : 3036 (243075 expanded)
%              Number of equality atoms :  388 (27822 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_mcart_1 @ X38 ) )
      | ( X38
       != ( k4_tarski @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_tarski @ X39 @ X40 )
     != ( k1_mcart_1 @ ( k4_tarski @ X39 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('2',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X58 @ X59 ) )
      = X58 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_tarski @ X39 @ X40 )
     != X39 ) ),
    inference(demod,[status(thm)],['1','2'])).

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

thf('4',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X35 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X8 )
      | ~ ( r2_hidden @ X3 @ X8 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( X5
       != ( k4_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X3 @ X8 )
      | ( zip_tseitin_0 @ X4 @ X3 @ ( k4_tarski @ X3 @ X4 ) @ X6 @ X8 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
      | ( zip_tseitin_0 @ sk_E_3 @ X1 @ ( k4_tarski @ X1 @ sk_E_3 ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( zip_tseitin_0 @ sk_E_3 @ ( k1_mcart_1 @ sk_E_3 ) @ ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ sk_E_3 ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( zip_tseitin_0 @ sk_E_3 @ ( k1_mcart_1 @ sk_E_3 ) @ ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ sk_E_3 ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X11 @ X14 )
      | ( X14
       != ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X13 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ sk_E_3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ sk_E_3 ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( m1_subset_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ sk_E_3 ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ sk_E_3 ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ sk_E_3 ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('37',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ sk_E_3 ) ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X58: $i,X60: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X58 @ X60 ) )
      = X60 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) )
    | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('42',plain,(
    ! [X44: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X44 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X35 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56 )
       != k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['55'])).

thf('57',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('58',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X19 ) @ ( sk_E_2 @ X19 ) )
        = X19 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D_1 @ X3 ) @ ( sk_E_2 @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
      = sk_E_3 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X53: $i,X54: $i,X55: $i,X57: $i] :
      ( ( X57 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X57 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('64',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('66',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X1 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('72',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X53: $i,X54: $i,X55: $i,X57: $i] :
      ( ( X53 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X57 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('77',plain,(
    ! [X54: $i,X55: $i,X57: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X54 @ X55 @ X57 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','75','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 ) ) ),
    inference(demod,[status(thm)],['62','78'])).

thf('80',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56 )
       != k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['82','83','84','85'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['82','83','84','85'])).

thf('91',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X58 @ X59 ) )
      = X58 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_E_3 )
        = ( sk_D_1 @ sk_E_3 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_E_3 )
        = ( sk_D_1 @ sk_E_3 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( sk_D_1 @ sk_E_3 ) )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( sk_D_1 @ sk_E_3 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_E_3 )
        = ( sk_D_1 @ sk_E_3 ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( k1_mcart_1 @ sk_E_3 )
    = ( sk_D_1 @ sk_E_3 ) ),
    inference(condensation,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D_1 @ sk_E_3 ) @ ( sk_E_2 @ sk_E_3 ) )
        = sk_E_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['82','83','84','85'])).

thf('98',plain,(
    ! [X58: $i,X60: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X58 @ X60 ) )
      = X60 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_E_3 )
        = ( sk_E_2 @ sk_E_3 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_E_3 )
        = ( sk_E_2 @ sk_E_3 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_mcart_1 @ sk_E_3 )
        = ( sk_E_2 @ sk_E_3 ) )
      | ( ( k2_mcart_1 @ sk_E_3 )
        = ( sk_E_2 @ sk_E_3 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ sk_E_3 )
        = ( sk_E_2 @ sk_E_3 ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( k2_mcart_1 @ sk_E_3 )
    = ( sk_E_2 @ sk_E_3 ) ),
    inference(condensation,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_mcart_1 @ sk_E_3 ) )
        = sk_E_3 )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['89','96','103'])).

thf('105',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_mcart_1 @ sk_E_3 ) )
    = sk_E_3 ),
    inference(condensation,[status(thm)],['104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('107',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('108',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( m1_subset_1 @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t24_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('109',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42
        = ( k4_tarski @ ( k1_mcart_1 @ X42 ) @ ( k2_mcart_1 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k2_zfmisc_1 @ X41 @ X43 ) )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_3 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E_3 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X44: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X44 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k1_mcart_1 @ sk_E_3 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','75','77'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56 )
       != k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['124','125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['124','125','126','127'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) )
      | ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_E_3 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( k1_mcart_1 @ sk_E_3 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) ) ),
    inference(condensation,[status(thm)],['131'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('133',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_mcart_1 @ X25 @ X26 @ X27 )
      = ( k4_tarski @ ( k4_tarski @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('136',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X15 @ X12 @ X13 ) @ ( sk_E_1 @ X15 @ X12 @ X13 ) @ X15 @ X12 @ X13 )
      | ( X14
       != ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('137',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X15 @ X12 @ X13 ) @ ( sk_E_1 @ X15 @ X12 @ X13 ) @ X15 @ X12 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) @ ( sk_E_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X6 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ sk_B_2 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X62 @ X61 @ X63 ) )
      | ( sk_D_2 = X63 )
      | ~ ( m1_subset_1 @ X63 @ sk_C )
      | ~ ( m1_subset_1 @ X62 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_2 = X1 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X0 @ ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) @ ( sk_E_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('146',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5
        = ( k4_tarski @ X3 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E_3 )
      = ( k4_tarski @ ( sk_E_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) @ ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X58: $i,X60: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X58 @ X60 ) )
      = X60 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('149',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
      = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
        = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56 )
       != k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
        = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
        = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
        = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['154','155','156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
        = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['154','155','156','157'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
        = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
        = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
        = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) )
    = ( sk_F_1 @ ( k1_mcart_1 @ sk_E_3 ) @ sk_B_2 @ sk_A ) ),
    inference(condensation,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_2 = X1 )
      | ( sk_E_3
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['144','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( sk_E_3
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['134','163'])).

thf('165',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('166',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X35 ) @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('167',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('169',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','75','77'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56 )
       != k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['176','177','178','179'])).

thf('181',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_tarski @ X39 @ X40 )
     != X39 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_3 ) ) @ sk_A ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( sk_E_3
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_3 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['164','185'])).

thf('187',plain,
    ( ( sk_E_3 != sk_E_3 )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C )
    | ( sk_D_2
      = ( k2_mcart_1 @ sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['105','186'])).

thf('188',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('190',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('192',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','75','77'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56 )
       != k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['199','200','201','202'])).

thf('204',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_tarski @ X39 @ X40 )
     != X39 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_3 ) @ sk_C ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( sk_E_3 != sk_E_3 )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_D_2
      = ( k2_mcart_1 @ sk_E_3 ) ) ),
    inference(demod,[status(thm)],['187','208'])).

thf('210',plain,
    ( ( sk_D_2
      = ( k2_mcart_1 @ sk_E_3 ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('213',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X49 @ X50 @ X52 @ X51 )
        = ( k2_mcart_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k3_zfmisc_1 @ X49 @ X50 @ X52 ) )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('214',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
      = ( k2_mcart_1 @ sk_E_3 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3 )
    = ( k2_mcart_1 @ sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['214','215','216','217'])).

thf('219',plain,(
    sk_D_2
 != ( k2_mcart_1 @ sk_E_3 ) ),
    inference(demod,[status(thm)],['211','218'])).

thf('220',plain,(
    v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['210','219'])).

thf('221',plain,(
    m1_subset_1 @ sk_E_3 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('223',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( v1_xboole_0 @ sk_E_3 ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['210','219'])).

thf('225',plain,(
    v1_xboole_0 @ sk_E_3 ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_E_3 = X0 ) ) ),
    inference('sup-',[status(thm)],['225','228'])).

thf('230',plain,
    ( sk_E_3
    = ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['220','229'])).

thf('231',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = ( k2_zfmisc_1 @ sk_E_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','75','77'])).

thf('234',plain,(
    v1_xboole_0 @ sk_E_3 ),
    inference(demod,[status(thm)],['223','224'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('236',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('238',plain,(
    ! [X1: $i] :
      ( sk_E_3
      = ( k2_zfmisc_1 @ sk_E_3 @ X1 ) ) ),
    inference(demod,[status(thm)],['233','236','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = sk_E_3 ) ),
    inference(demod,[status(thm)],['232','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('241',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56 )
       != k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('242',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('245',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('246',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('247',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('248',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X1 = sk_E_3 )
      | ( X2 = sk_E_3 )
      | ( X3 = sk_E_3 )
      | ( X4 = sk_E_3 )
      | ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['243','244','245','246','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_E_3 )
      | ( sk_A = sk_E_3 )
      | ( sk_B_2 = sk_E_3 )
      | ( sk_C = sk_E_3 )
      | ( X0 = sk_E_3 ) ) ),
    inference('sup-',[status(thm)],['239','248'])).

thf('250',plain,(
    v1_xboole_0 @ sk_E_3 ),
    inference(demod,[status(thm)],['223','224'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_E_3 )
      | ( sk_B_2 = sk_E_3 )
      | ( sk_C = sk_E_3 )
      | ( X0 = sk_E_3 ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('254',plain,(
    sk_C != sk_E_3 ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('257',plain,(
    sk_B_2 != sk_E_3 ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    sk_E_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['234','235'])).

thf('260',plain,(
    sk_A != sk_E_3 ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i] : ( X0 = sk_E_3 ) ),
    inference('simplify_reflect-',[status(thm)],['251','254','257','260'])).

thf('262',plain,(
    ! [X39: $i] : ( sk_E_3 != X39 ) ),
    inference(demod,[status(thm)],['3','261'])).

thf('263',plain,(
    $false ),
    inference(simplify,[status(thm)],['262'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Scq9loWCZ
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.53/8.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.53/8.74  % Solved by: fo/fo7.sh
% 8.53/8.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.53/8.74  % done 8645 iterations in 8.282s
% 8.53/8.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.53/8.74  % SZS output start Refutation
% 8.53/8.74  thf(sk_D_2_type, type, sk_D_2: $i).
% 8.53/8.74  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 8.53/8.74  thf(sk_C_type, type, sk_C: $i).
% 8.53/8.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.53/8.74  thf(sk_E_2_type, type, sk_E_2: $i > $i).
% 8.53/8.74  thf(sk_B_2_type, type, sk_B_2: $i).
% 8.53/8.74  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 8.53/8.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.53/8.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.53/8.74  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 8.53/8.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 8.53/8.74  thf(sk_B_type, type, sk_B: $i > $i).
% 8.53/8.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.53/8.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.53/8.74  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 8.53/8.74  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 8.53/8.74  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 8.53/8.74  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 8.53/8.74  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 8.53/8.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 8.53/8.74  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 8.53/8.74  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 8.53/8.74  thf(sk_A_type, type, sk_A: $i).
% 8.53/8.74  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 8.53/8.74  thf(sk_E_3_type, type, sk_E_3: $i).
% 8.53/8.74  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 8.53/8.74  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 8.53/8.74  thf(t20_mcart_1, axiom,
% 8.53/8.74    (![A:$i]:
% 8.53/8.74     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 8.53/8.74       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 8.53/8.74  thf('0', plain,
% 8.53/8.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 8.53/8.74         (((X38) != (k1_mcart_1 @ X38)) | ((X38) != (k4_tarski @ X39 @ X40)))),
% 8.53/8.74      inference('cnf', [status(esa)], [t20_mcart_1])).
% 8.53/8.74  thf('1', plain,
% 8.53/8.74      (![X39 : $i, X40 : $i]:
% 8.53/8.74         ((k4_tarski @ X39 @ X40) != (k1_mcart_1 @ (k4_tarski @ X39 @ X40)))),
% 8.53/8.74      inference('simplify', [status(thm)], ['0'])).
% 8.53/8.74  thf(t7_mcart_1, axiom,
% 8.53/8.74    (![A:$i,B:$i]:
% 8.53/8.74     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 8.53/8.74       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 8.53/8.74  thf('2', plain,
% 8.53/8.74      (![X58 : $i, X59 : $i]: ((k1_mcart_1 @ (k4_tarski @ X58 @ X59)) = (X58))),
% 8.53/8.74      inference('cnf', [status(esa)], [t7_mcart_1])).
% 8.53/8.74  thf('3', plain, (![X39 : $i, X40 : $i]: ((k4_tarski @ X39 @ X40) != (X39))),
% 8.53/8.74      inference('demod', [status(thm)], ['1', '2'])).
% 8.53/8.74  thf(t71_mcart_1, conjecture,
% 8.53/8.74    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.53/8.74     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 8.53/8.74       ( ( ![F:$i]:
% 8.53/8.74           ( ( m1_subset_1 @ F @ A ) =>
% 8.53/8.74             ( ![G:$i]:
% 8.53/8.74               ( ( m1_subset_1 @ G @ B ) =>
% 8.53/8.74                 ( ![H:$i]:
% 8.53/8.74                   ( ( m1_subset_1 @ H @ C ) =>
% 8.53/8.74                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 8.53/8.74                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 8.53/8.74         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.53/8.74           ( ( C ) = ( k1_xboole_0 ) ) | 
% 8.53/8.74           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 8.53/8.74  thf(zf_stmt_0, negated_conjecture,
% 8.53/8.74    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.53/8.74        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 8.53/8.74          ( ( ![F:$i]:
% 8.53/8.74              ( ( m1_subset_1 @ F @ A ) =>
% 8.53/8.74                ( ![G:$i]:
% 8.53/8.74                  ( ( m1_subset_1 @ G @ B ) =>
% 8.53/8.74                    ( ![H:$i]:
% 8.53/8.74                      ( ( m1_subset_1 @ H @ C ) =>
% 8.53/8.74                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 8.53/8.74                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 8.53/8.74            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.53/8.74              ( ( C ) = ( k1_xboole_0 ) ) | 
% 8.53/8.74              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 8.53/8.74    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 8.53/8.74  thf('4', plain,
% 8.53/8.74      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 8.53/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.74  thf(d2_subset_1, axiom,
% 8.53/8.74    (![A:$i,B:$i]:
% 8.53/8.74     ( ( ( v1_xboole_0 @ A ) =>
% 8.53/8.74         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 8.53/8.74       ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.53/8.74         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 8.53/8.74  thf('5', plain,
% 8.53/8.74      (![X22 : $i, X23 : $i]:
% 8.53/8.74         (~ (m1_subset_1 @ X22 @ X23)
% 8.53/8.74          | (r2_hidden @ X22 @ X23)
% 8.53/8.74          | (v1_xboole_0 @ X23))),
% 8.53/8.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.53/8.74  thf('6', plain,
% 8.53/8.74      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74        | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.74      inference('sup-', [status(thm)], ['4', '5'])).
% 8.53/8.74  thf(d3_zfmisc_1, axiom,
% 8.53/8.74    (![A:$i,B:$i,C:$i]:
% 8.53/8.74     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 8.53/8.74       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 8.53/8.74  thf('7', plain,
% 8.53/8.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.74         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 8.53/8.74           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 8.53/8.74      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 8.53/8.74  thf(t10_mcart_1, axiom,
% 8.53/8.74    (![A:$i,B:$i,C:$i]:
% 8.53/8.74     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 8.53/8.74       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 8.53/8.74         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 8.53/8.74  thf('8', plain,
% 8.53/8.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 8.53/8.74         ((r2_hidden @ (k1_mcart_1 @ X35) @ X36)
% 8.53/8.74          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 8.53/8.74      inference('cnf', [status(esa)], [t10_mcart_1])).
% 8.53/8.74  thf('9', plain,
% 8.53/8.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.74         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 8.53/8.74          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 8.53/8.74      inference('sup-', [status(thm)], ['7', '8'])).
% 8.53/8.74  thf('10', plain,
% 8.53/8.74      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74        | (r2_hidden @ (k1_mcart_1 @ sk_E_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.53/8.74      inference('sup-', [status(thm)], ['6', '9'])).
% 8.53/8.74  thf('11', plain,
% 8.53/8.74      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74        | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.74      inference('sup-', [status(thm)], ['4', '5'])).
% 8.53/8.74  thf(d2_zfmisc_1, axiom,
% 8.53/8.74    (![A:$i,B:$i,C:$i]:
% 8.53/8.74     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 8.53/8.74       ( ![D:$i]:
% 8.53/8.74         ( ( r2_hidden @ D @ C ) <=>
% 8.53/8.74           ( ?[E:$i,F:$i]:
% 8.53/8.74             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 8.53/8.74               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 8.53/8.74  thf(zf_stmt_1, axiom,
% 8.53/8.74    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 8.53/8.74     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 8.53/8.74       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 8.53/8.74         ( r2_hidden @ E @ A ) ) ))).
% 8.53/8.74  thf('12', plain,
% 8.53/8.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X8 : $i]:
% 8.53/8.74         ((zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X8)
% 8.53/8.74          | ~ (r2_hidden @ X3 @ X8)
% 8.53/8.74          | ~ (r2_hidden @ X4 @ X6)
% 8.53/8.74          | ((X5) != (k4_tarski @ X3 @ X4)))),
% 8.53/8.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.53/8.74  thf('13', plain,
% 8.53/8.74      (![X3 : $i, X4 : $i, X6 : $i, X8 : $i]:
% 8.53/8.74         (~ (r2_hidden @ X4 @ X6)
% 8.53/8.74          | ~ (r2_hidden @ X3 @ X8)
% 8.53/8.74          | (zip_tseitin_0 @ X4 @ X3 @ (k4_tarski @ X3 @ X4) @ X6 @ X8))),
% 8.53/8.74      inference('simplify', [status(thm)], ['12'])).
% 8.53/8.74  thf('14', plain,
% 8.53/8.74      (![X0 : $i, X1 : $i]:
% 8.53/8.74         ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74          | (zip_tseitin_0 @ sk_E_3 @ X1 @ (k4_tarski @ X1 @ sk_E_3) @ 
% 8.53/8.74             (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ X0)
% 8.53/8.74          | ~ (r2_hidden @ X1 @ X0))),
% 8.53/8.74      inference('sup-', [status(thm)], ['11', '13'])).
% 8.53/8.74  thf('15', plain,
% 8.53/8.74      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74        | (zip_tseitin_0 @ sk_E_3 @ (k1_mcart_1 @ sk_E_3) @ 
% 8.53/8.74           (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ sk_E_3) @ 
% 8.53/8.74           (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 8.53/8.74        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.74      inference('sup-', [status(thm)], ['10', '14'])).
% 8.53/8.74  thf('16', plain,
% 8.53/8.74      (((zip_tseitin_0 @ sk_E_3 @ (k1_mcart_1 @ sk_E_3) @ 
% 8.53/8.74         (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ sk_E_3) @ 
% 8.53/8.74         (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 8.53/8.74        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.74      inference('simplify', [status(thm)], ['15'])).
% 8.53/8.74  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 8.53/8.74  thf(zf_stmt_3, axiom,
% 8.53/8.74    (![A:$i,B:$i,C:$i]:
% 8.53/8.74     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 8.53/8.74       ( ![D:$i]:
% 8.53/8.74         ( ( r2_hidden @ D @ C ) <=>
% 8.53/8.74           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 8.53/8.74  thf('17', plain,
% 8.53/8.74      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 8.53/8.74         (~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13)
% 8.53/8.74          | (r2_hidden @ X11 @ X14)
% 8.53/8.74          | ((X14) != (k2_zfmisc_1 @ X13 @ X12)))),
% 8.53/8.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.53/8.74  thf('18', plain,
% 8.53/8.74      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 8.53/8.74         ((r2_hidden @ X11 @ (k2_zfmisc_1 @ X13 @ X12))
% 8.53/8.74          | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 @ X13))),
% 8.53/8.74      inference('simplify', [status(thm)], ['17'])).
% 8.53/8.74  thf('19', plain,
% 8.53/8.74      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74        | (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ sk_E_3) @ 
% 8.53/8.74           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2) @ 
% 8.53/8.74            (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))))),
% 8.53/8.74      inference('sup-', [status(thm)], ['16', '18'])).
% 8.53/8.74  thf('20', plain,
% 8.53/8.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.74         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 8.53/8.74           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 8.53/8.74      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 8.53/8.74  thf('21', plain,
% 8.53/8.74      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74        | (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ sk_E_3) @ 
% 8.53/8.74           (k3_zfmisc_1 @ sk_A @ sk_B_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))))),
% 8.53/8.74      inference('demod', [status(thm)], ['19', '20'])).
% 8.53/8.74  thf('22', plain,
% 8.53/8.74      (![X22 : $i, X23 : $i]:
% 8.53/8.74         (~ (r2_hidden @ X22 @ X23)
% 8.53/8.74          | (m1_subset_1 @ X22 @ X23)
% 8.53/8.74          | (v1_xboole_0 @ X23))),
% 8.53/8.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.53/8.74  thf(d1_xboole_0, axiom,
% 8.53/8.74    (![A:$i]:
% 8.53/8.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 8.53/8.74  thf('23', plain,
% 8.53/8.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 8.53/8.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.53/8.74  thf('24', plain,
% 8.53/8.74      (![X22 : $i, X23 : $i]:
% 8.53/8.74         ((m1_subset_1 @ X22 @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 8.53/8.74      inference('clc', [status(thm)], ['22', '23'])).
% 8.53/8.74  thf('25', plain,
% 8.53/8.74      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74        | (m1_subset_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ sk_E_3) @ 
% 8.53/8.74           (k3_zfmisc_1 @ sk_A @ sk_B_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))))),
% 8.53/8.74      inference('sup-', [status(thm)], ['21', '24'])).
% 8.53/8.74  thf('26', plain,
% 8.53/8.74      (![X22 : $i, X23 : $i]:
% 8.53/8.74         (~ (m1_subset_1 @ X22 @ X23)
% 8.53/8.74          | (r2_hidden @ X22 @ X23)
% 8.53/8.74          | (v1_xboole_0 @ X23))),
% 8.53/8.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.53/8.74  thf('27', plain,
% 8.53/8.74      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.74        | (v1_xboole_0 @ 
% 8.53/8.74           (k3_zfmisc_1 @ sk_A @ sk_B_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))
% 8.53/8.74        | (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ sk_E_3) @ 
% 8.53/8.74           (k3_zfmisc_1 @ sk_A @ sk_B_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))))),
% 8.53/8.74      inference('sup-', [status(thm)], ['25', '26'])).
% 8.53/8.74  thf('28', plain,
% 8.53/8.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 8.53/8.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 8.53/8.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 8.53/8.75  thf('29', plain,
% 8.53/8.75      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 8.53/8.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.53/8.75  thf('30', plain,
% 8.53/8.75      (![X35 : $i, X36 : $i, X37 : $i]:
% 8.53/8.75         ((r2_hidden @ (k2_mcart_1 @ X35) @ X37)
% 8.53/8.75          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t10_mcart_1])).
% 8.53/8.75  thf('31', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 8.53/8.75          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['29', '30'])).
% 8.53/8.75  thf('32', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 8.53/8.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.53/8.75  thf('33', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['31', '32'])).
% 8.53/8.75  thf('34', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.53/8.75         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup+', [status(thm)], ['28', '33'])).
% 8.53/8.75  thf('35', plain,
% 8.53/8.75      (((r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ sk_E_3) @ 
% 8.53/8.75         (k3_zfmisc_1 @ sk_A @ sk_B_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))
% 8.53/8.75        | (v1_xboole_0 @ 
% 8.53/8.75           (k3_zfmisc_1 @ sk_A @ sk_B_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))))),
% 8.53/8.75      inference('clc', [status(thm)], ['27', '34'])).
% 8.53/8.75  thf('36', plain,
% 8.53/8.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 8.53/8.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 8.53/8.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 8.53/8.75  thf('37', plain,
% 8.53/8.75      (![X35 : $i, X36 : $i, X37 : $i]:
% 8.53/8.75         ((r2_hidden @ (k2_mcart_1 @ X35) @ X37)
% 8.53/8.75          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t10_mcart_1])).
% 8.53/8.75  thf('38', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 8.53/8.75          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['36', '37'])).
% 8.53/8.75  thf('39', plain,
% 8.53/8.75      (((v1_xboole_0 @ 
% 8.53/8.75         (k3_zfmisc_1 @ sk_A @ sk_B_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))
% 8.53/8.75        | (r2_hidden @ 
% 8.53/8.75           (k2_mcart_1 @ (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ sk_E_3)) @ 
% 8.53/8.75           (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['35', '38'])).
% 8.53/8.75  thf('40', plain,
% 8.53/8.75      (![X58 : $i, X60 : $i]: ((k2_mcart_1 @ (k4_tarski @ X58 @ X60)) = (X60))),
% 8.53/8.75      inference('cnf', [status(esa)], [t7_mcart_1])).
% 8.53/8.75  thf('41', plain,
% 8.53/8.75      (((v1_xboole_0 @ 
% 8.53/8.75         (k3_zfmisc_1 @ sk_A @ sk_B_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))
% 8.53/8.75        | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('demod', [status(thm)], ['39', '40'])).
% 8.53/8.75  thf(t34_mcart_1, axiom,
% 8.53/8.75    (![A:$i]:
% 8.53/8.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 8.53/8.75          ( ![B:$i]:
% 8.53/8.75            ( ~( ( r2_hidden @ B @ A ) & 
% 8.53/8.75                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 8.53/8.75                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 8.53/8.75                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 8.53/8.75  thf('42', plain,
% 8.53/8.75      (![X44 : $i]:
% 8.53/8.75         (((X44) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X44) @ X44))),
% 8.53/8.75      inference('cnf', [status(esa)], [t34_mcart_1])).
% 8.53/8.75  thf('43', plain,
% 8.53/8.75      (![X35 : $i, X36 : $i, X37 : $i]:
% 8.53/8.75         ((r2_hidden @ (k1_mcart_1 @ X35) @ X36)
% 8.53/8.75          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t10_mcart_1])).
% 8.53/8.75  thf('44', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 8.53/8.75      inference('sup-', [status(thm)], ['42', '43'])).
% 8.53/8.75  thf('45', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 8.53/8.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.53/8.75  thf('46', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['44', '45'])).
% 8.53/8.75  thf(d4_zfmisc_1, axiom,
% 8.53/8.75    (![A:$i,B:$i,C:$i,D:$i]:
% 8.53/8.75     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 8.53/8.75       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 8.53/8.75  thf('47', plain,
% 8.53/8.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 8.53/8.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 8.53/8.75  thf('48', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 8.53/8.75          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['46', '47'])).
% 8.53/8.75  thf('49', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         ((r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75          | ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ 
% 8.53/8.75              (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['41', '48'])).
% 8.53/8.75  thf(t55_mcart_1, axiom,
% 8.53/8.75    (![A:$i,B:$i,C:$i,D:$i]:
% 8.53/8.75     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 8.53/8.75         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 8.53/8.75       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 8.53/8.75  thf('50', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56) != (k1_xboole_0))
% 8.53/8.75          | ((X56) = (k1_xboole_0))
% 8.53/8.75          | ((X55) = (k1_xboole_0))
% 8.53/8.75          | ((X54) = (k1_xboole_0))
% 8.53/8.75          | ((X53) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('51', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_xboole_0) != (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['49', '50'])).
% 8.53/8.75  thf('52', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['51'])).
% 8.53/8.75  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('54', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('55', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)], ['52', '53', '54'])).
% 8.53/8.75  thf('56', plain,
% 8.53/8.75      (((r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 8.53/8.75      inference('condensation', [status(thm)], ['55'])).
% 8.53/8.75  thf('57', plain,
% 8.53/8.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 8.53/8.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 8.53/8.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 8.53/8.75  thf(l139_zfmisc_1, axiom,
% 8.53/8.75    (![A:$i,B:$i,C:$i]:
% 8.53/8.75     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 8.53/8.75          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 8.53/8.75  thf('58', plain,
% 8.53/8.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.53/8.75         (((k4_tarski @ (sk_D_1 @ X19) @ (sk_E_2 @ X19)) = (X19))
% 8.53/8.75          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 8.53/8.75      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 8.53/8.75  thf('59', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ X3) @ (sk_E_2 @ X3)) = (X3)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['57', '58'])).
% 8.53/8.75  thf('60', plain,
% 8.53/8.75      ((((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 8.53/8.75        | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['56', '59'])).
% 8.53/8.75  thf('61', plain,
% 8.53/8.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 8.53/8.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 8.53/8.75  thf('62', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 8.53/8.75            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['60', '61'])).
% 8.53/8.75  thf('63', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X57 : $i]:
% 8.53/8.75         (((X57) != (k1_xboole_0))
% 8.53/8.75          | ((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X57) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('64', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X53 @ X54 @ X55 @ k1_xboole_0) = (k1_xboole_0))),
% 8.53/8.75      inference('simplify', [status(thm)], ['63'])).
% 8.53/8.75  thf('65', plain,
% 8.53/8.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 8.53/8.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 8.53/8.75  thf('66', plain,
% 8.53/8.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 8.53/8.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 8.53/8.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 8.53/8.75  thf('67', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 8.53/8.75           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 8.53/8.75      inference('sup+', [status(thm)], ['65', '66'])).
% 8.53/8.75  thf('68', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ k1_xboole_0 @ X0)
% 8.53/8.75           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup+', [status(thm)], ['64', '67'])).
% 8.53/8.75  thf('69', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ k1_xboole_0 @ X0)
% 8.53/8.75           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup+', [status(thm)], ['64', '67'])).
% 8.53/8.75  thf('70', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ X1)
% 8.53/8.75           = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 8.53/8.75      inference('sup+', [status(thm)], ['68', '69'])).
% 8.53/8.75  thf('71', plain,
% 8.53/8.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 8.53/8.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 8.53/8.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 8.53/8.75  thf('72', plain,
% 8.53/8.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ X28 @ X29 @ X30)
% 8.53/8.75           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29) @ X30))),
% 8.53/8.75      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 8.53/8.75  thf('73', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 8.53/8.75      inference('sup+', [status(thm)], ['71', '72'])).
% 8.53/8.75  thf('74', plain,
% 8.53/8.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 8.53/8.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 8.53/8.75  thf('75', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 8.53/8.75           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 8.53/8.75      inference('demod', [status(thm)], ['73', '74'])).
% 8.53/8.75  thf('76', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X57 : $i]:
% 8.53/8.75         (((X53) != (k1_xboole_0))
% 8.53/8.75          | ((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X57) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('77', plain,
% 8.53/8.75      (![X54 : $i, X55 : $i, X57 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ k1_xboole_0 @ X54 @ X55 @ X57) = (k1_xboole_0))),
% 8.53/8.75      inference('simplify', [status(thm)], ['76'])).
% 8.53/8.75  thf('78', plain,
% 8.53/8.75      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 8.53/8.75      inference('demod', [status(thm)], ['70', '75', '77'])).
% 8.53/8.75  thf('79', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('demod', [status(thm)], ['62', '78'])).
% 8.53/8.75  thf('80', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56) != (k1_xboole_0))
% 8.53/8.75          | ((X56) = (k1_xboole_0))
% 8.53/8.75          | ((X55) = (k1_xboole_0))
% 8.53/8.75          | ((X54) = (k1_xboole_0))
% 8.53/8.75          | ((X53) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('81', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_xboole_0) != (k1_xboole_0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['79', '80'])).
% 8.53/8.75  thf('82', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['81'])).
% 8.53/8.75  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('84', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('85', plain, (((sk_C) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('86', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)], ['82', '83', '84', '85'])).
% 8.53/8.75  thf('87', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)], ['82', '83', '84', '85'])).
% 8.53/8.75  thf('88', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((X1) = (X0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['86', '87'])).
% 8.53/8.75  thf('89', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3))
% 8.53/8.75          | ((X1) = (X0)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['88'])).
% 8.53/8.75  thf('90', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)], ['82', '83', '84', '85'])).
% 8.53/8.75  thf('91', plain,
% 8.53/8.75      (![X58 : $i, X59 : $i]: ((k1_mcart_1 @ (k4_tarski @ X58 @ X59)) = (X58))),
% 8.53/8.75      inference('cnf', [status(esa)], [t7_mcart_1])).
% 8.53/8.75  thf('92', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_mcart_1 @ sk_E_3) = (sk_D_1 @ sk_E_3)) | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['90', '91'])).
% 8.53/8.75  thf('93', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_mcart_1 @ sk_E_3) = (sk_D_1 @ sk_E_3)) | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['90', '91'])).
% 8.53/8.75  thf('94', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((X1) = (X0))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3) = (sk_D_1 @ sk_E_3))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3) = (sk_D_1 @ sk_E_3)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['92', '93'])).
% 8.53/8.75  thf('95', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((k1_mcart_1 @ sk_E_3) = (sk_D_1 @ sk_E_3)) | ((X1) = (X0)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['94'])).
% 8.53/8.75  thf('96', plain, (((k1_mcart_1 @ sk_E_3) = (sk_D_1 @ sk_E_3))),
% 8.53/8.75      inference('condensation', [status(thm)], ['95'])).
% 8.53/8.75  thf('97', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k4_tarski @ (sk_D_1 @ sk_E_3) @ (sk_E_2 @ sk_E_3)) = (sk_E_3)))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)], ['82', '83', '84', '85'])).
% 8.53/8.75  thf('98', plain,
% 8.53/8.75      (![X58 : $i, X60 : $i]: ((k2_mcart_1 @ (k4_tarski @ X58 @ X60)) = (X60))),
% 8.53/8.75      inference('cnf', [status(esa)], [t7_mcart_1])).
% 8.53/8.75  thf('99', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3)) | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['97', '98'])).
% 8.53/8.75  thf('100', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3)) | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['97', '98'])).
% 8.53/8.75  thf('101', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((X1) = (X0))
% 8.53/8.75          | ((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3))
% 8.53/8.75          | ((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['99', '100'])).
% 8.53/8.75  thf('102', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3)) | ((X1) = (X0)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['101'])).
% 8.53/8.75  thf('103', plain, (((k2_mcart_1 @ sk_E_3) = (sk_E_2 @ sk_E_3))),
% 8.53/8.75      inference('condensation', [status(thm)], ['102'])).
% 8.53/8.75  thf('104', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((k4_tarski @ (k1_mcart_1 @ sk_E_3) @ (k2_mcart_1 @ sk_E_3))
% 8.53/8.75            = (sk_E_3))
% 8.53/8.75          | ((X1) = (X0)))),
% 8.53/8.75      inference('demod', [status(thm)], ['89', '96', '103'])).
% 8.53/8.75  thf('105', plain,
% 8.53/8.75      (((k4_tarski @ (k1_mcart_1 @ sk_E_3) @ (k2_mcart_1 @ sk_E_3)) = (sk_E_3))),
% 8.53/8.75      inference('condensation', [status(thm)], ['104'])).
% 8.53/8.75  thf('106', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (r2_hidden @ (k1_mcart_1 @ sk_E_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['6', '9'])).
% 8.53/8.75  thf('107', plain,
% 8.53/8.75      (![X22 : $i, X23 : $i]:
% 8.53/8.75         ((m1_subset_1 @ X22 @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 8.53/8.75      inference('clc', [status(thm)], ['22', '23'])).
% 8.53/8.75  thf('108', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (m1_subset_1 @ (k1_mcart_1 @ sk_E_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['106', '107'])).
% 8.53/8.75  thf(t24_mcart_1, axiom,
% 8.53/8.75    (![A:$i,B:$i]:
% 8.53/8.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 8.53/8.75          ( ~( ![C:$i]:
% 8.53/8.75               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 8.53/8.75                 ( ( C ) =
% 8.53/8.75                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 8.53/8.75  thf('109', plain,
% 8.53/8.75      (![X41 : $i, X42 : $i, X43 : $i]:
% 8.53/8.75         (((X41) = (k1_xboole_0))
% 8.53/8.75          | ((X42) = (k4_tarski @ (k1_mcart_1 @ X42) @ (k2_mcart_1 @ X42)))
% 8.53/8.75          | ~ (m1_subset_1 @ X42 @ (k2_zfmisc_1 @ X41 @ X43))
% 8.53/8.75          | ((X43) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t24_mcart_1])).
% 8.53/8.75  thf('110', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75        | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))))
% 8.53/8.75        | ((sk_A) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['108', '109'])).
% 8.53/8.75  thf('111', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('112', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('113', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)], ['110', '111', '112'])).
% 8.53/8.75  thf('114', plain,
% 8.53/8.75      (![X44 : $i]:
% 8.53/8.75         (((X44) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X44) @ X44))),
% 8.53/8.75      inference('cnf', [status(esa)], [t34_mcart_1])).
% 8.53/8.75  thf('115', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 8.53/8.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.53/8.75  thf('116', plain,
% 8.53/8.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['114', '115'])).
% 8.53/8.75  thf('117', plain,
% 8.53/8.75      ((((k1_mcart_1 @ sk_E_3)
% 8.53/8.75          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75             (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))))
% 8.53/8.75        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['113', '116'])).
% 8.53/8.75  thf('118', plain,
% 8.53/8.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 8.53/8.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 8.53/8.75  thf('119', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 8.53/8.75            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))))),
% 8.53/8.75      inference('sup+', [status(thm)], ['117', '118'])).
% 8.53/8.75  thf('120', plain,
% 8.53/8.75      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 8.53/8.75      inference('demod', [status(thm)], ['70', '75', '77'])).
% 8.53/8.75  thf('121', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))))),
% 8.53/8.75      inference('demod', [status(thm)], ['119', '120'])).
% 8.53/8.75  thf('122', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56) != (k1_xboole_0))
% 8.53/8.75          | ((X56) = (k1_xboole_0))
% 8.53/8.75          | ((X55) = (k1_xboole_0))
% 8.53/8.75          | ((X54) = (k1_xboole_0))
% 8.53/8.75          | ((X53) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('123', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_xboole_0) != (k1_xboole_0))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['121', '122'])).
% 8.53/8.75  thf('124', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))))),
% 8.53/8.75      inference('simplify', [status(thm)], ['123'])).
% 8.53/8.75  thf('125', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('126', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('127', plain, (((sk_C) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('128', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)],
% 8.53/8.75                ['124', '125', '126', '127'])).
% 8.53/8.75  thf('129', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)],
% 8.53/8.75                ['124', '125', '126', '127'])).
% 8.53/8.75  thf('130', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((X1) = (X0))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))))
% 8.53/8.75          | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)))))),
% 8.53/8.75      inference('sup+', [status(thm)], ['128', '129'])).
% 8.53/8.75  thf('131', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((k1_mcart_1 @ sk_E_3)
% 8.53/8.75            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))))
% 8.53/8.75          | ((X1) = (X0)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['130'])).
% 8.53/8.75  thf('132', plain,
% 8.53/8.75      (((k1_mcart_1 @ sk_E_3)
% 8.53/8.75         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))))),
% 8.53/8.75      inference('condensation', [status(thm)], ['131'])).
% 8.53/8.75  thf(d3_mcart_1, axiom,
% 8.53/8.75    (![A:$i,B:$i,C:$i]:
% 8.53/8.75     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 8.53/8.75  thf('133', plain,
% 8.53/8.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 8.53/8.75         ((k3_mcart_1 @ X25 @ X26 @ X27)
% 8.53/8.75           = (k4_tarski @ (k4_tarski @ X25 @ X26) @ X27))),
% 8.53/8.75      inference('cnf', [status(esa)], [d3_mcart_1])).
% 8.53/8.75  thf('134', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ 
% 8.53/8.75           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ X0)
% 8.53/8.75           = (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))),
% 8.53/8.75      inference('sup+', [status(thm)], ['132', '133'])).
% 8.53/8.75  thf('135', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (r2_hidden @ (k1_mcart_1 @ sk_E_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['6', '9'])).
% 8.53/8.75  thf('136', plain,
% 8.53/8.75      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 8.53/8.75         (~ (r2_hidden @ X15 @ X14)
% 8.53/8.75          | (zip_tseitin_0 @ (sk_F_1 @ X15 @ X12 @ X13) @ 
% 8.53/8.75             (sk_E_1 @ X15 @ X12 @ X13) @ X15 @ X12 @ X13)
% 8.53/8.75          | ((X14) != (k2_zfmisc_1 @ X13 @ X12)))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.53/8.75  thf('137', plain,
% 8.53/8.75      (![X12 : $i, X13 : $i, X15 : $i]:
% 8.53/8.75         ((zip_tseitin_0 @ (sk_F_1 @ X15 @ X12 @ X13) @ 
% 8.53/8.75           (sk_E_1 @ X15 @ X12 @ X13) @ X15 @ X12 @ X13)
% 8.53/8.75          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X13 @ X12)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['136'])).
% 8.53/8.75  thf('138', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (zip_tseitin_0 @ (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A) @ 
% 8.53/8.75           (sk_E_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A) @ 
% 8.53/8.75           (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))),
% 8.53/8.75      inference('sup-', [status(thm)], ['135', '137'])).
% 8.53/8.75  thf('139', plain,
% 8.53/8.75      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 8.53/8.75         ((r2_hidden @ X4 @ X6) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.53/8.75  thf('140', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (r2_hidden @ (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A) @ 
% 8.53/8.75           sk_B_2))),
% 8.53/8.75      inference('sup-', [status(thm)], ['138', '139'])).
% 8.53/8.75  thf('141', plain,
% 8.53/8.75      (![X22 : $i, X23 : $i]:
% 8.53/8.75         ((m1_subset_1 @ X22 @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 8.53/8.75      inference('clc', [status(thm)], ['22', '23'])).
% 8.53/8.75  thf('142', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (m1_subset_1 @ (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A) @ 
% 8.53/8.75           sk_B_2))),
% 8.53/8.75      inference('sup-', [status(thm)], ['140', '141'])).
% 8.53/8.75  thf('143', plain,
% 8.53/8.75      (![X61 : $i, X62 : $i, X63 : $i]:
% 8.53/8.75         (~ (m1_subset_1 @ X61 @ sk_B_2)
% 8.53/8.75          | ((sk_E_3) != (k3_mcart_1 @ X62 @ X61 @ X63))
% 8.53/8.75          | ((sk_D_2) = (X63))
% 8.53/8.75          | ~ (m1_subset_1 @ X63 @ sk_C)
% 8.53/8.75          | ~ (m1_subset_1 @ X62 @ sk_A))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('144', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75          | ~ (m1_subset_1 @ X0 @ sk_A)
% 8.53/8.75          | ~ (m1_subset_1 @ X1 @ sk_C)
% 8.53/8.75          | ((sk_D_2) = (X1))
% 8.53/8.75          | ((sk_E_3)
% 8.53/8.75              != (k3_mcart_1 @ X0 @ 
% 8.53/8.75                  (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A) @ X1)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['142', '143'])).
% 8.53/8.75  thf('145', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (zip_tseitin_0 @ (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A) @ 
% 8.53/8.75           (sk_E_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A) @ 
% 8.53/8.75           (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))),
% 8.53/8.75      inference('sup-', [status(thm)], ['135', '137'])).
% 8.53/8.75  thf('146', plain,
% 8.53/8.75      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 8.53/8.75         (((X5) = (k4_tarski @ X3 @ X4))
% 8.53/8.75          | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.53/8.75  thf('147', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | ((k1_mcart_1 @ sk_E_3)
% 8.53/8.75            = (k4_tarski @ (sk_E_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A) @ 
% 8.53/8.75               (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))))),
% 8.53/8.75      inference('sup-', [status(thm)], ['145', '146'])).
% 8.53/8.75  thf('148', plain,
% 8.53/8.75      (![X58 : $i, X60 : $i]: ((k2_mcart_1 @ (k4_tarski @ X58 @ X60)) = (X60))),
% 8.53/8.75      inference('cnf', [status(esa)], [t7_mcart_1])).
% 8.53/8.75  thf('149', plain,
% 8.53/8.75      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75          = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))
% 8.53/8.75        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['147', '148'])).
% 8.53/8.75  thf('150', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 8.53/8.75          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['46', '47'])).
% 8.53/8.75  thf('151', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75            = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))
% 8.53/8.75          | ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['149', '150'])).
% 8.53/8.75  thf('152', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56) != (k1_xboole_0))
% 8.53/8.75          | ((X56) = (k1_xboole_0))
% 8.53/8.75          | ((X55) = (k1_xboole_0))
% 8.53/8.75          | ((X54) = (k1_xboole_0))
% 8.53/8.75          | ((X53) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('153', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_xboole_0) != (k1_xboole_0))
% 8.53/8.75          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75              = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['151', '152'])).
% 8.53/8.75  thf('154', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75              = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['153'])).
% 8.53/8.75  thf('155', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('156', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('157', plain, (((sk_C) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('158', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75              = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A)))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)],
% 8.53/8.75                ['154', '155', '156', '157'])).
% 8.53/8.75  thf('159', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75              = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A)))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)],
% 8.53/8.75                ['154', '155', '156', '157'])).
% 8.53/8.75  thf('160', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((X1) = (X0))
% 8.53/8.75          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75              = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))
% 8.53/8.75          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75              = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A)))),
% 8.53/8.75      inference('sup+', [status(thm)], ['158', '159'])).
% 8.53/8.75  thf('161', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75            = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))
% 8.53/8.75          | ((X1) = (X0)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['160'])).
% 8.53/8.75  thf('162', plain,
% 8.53/8.75      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_3))
% 8.53/8.75         = (sk_F_1 @ (k1_mcart_1 @ sk_E_3) @ sk_B_2 @ sk_A))),
% 8.53/8.75      inference('condensation', [status(thm)], ['161'])).
% 8.53/8.75  thf('163', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75          | ~ (m1_subset_1 @ X0 @ sk_A)
% 8.53/8.75          | ~ (m1_subset_1 @ X1 @ sk_C)
% 8.53/8.75          | ((sk_D_2) = (X1))
% 8.53/8.75          | ((sk_E_3)
% 8.53/8.75              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ X1)))),
% 8.53/8.75      inference('demod', [status(thm)], ['144', '162'])).
% 8.53/8.75  thf('164', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((sk_E_3) != (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))
% 8.53/8.75          | ((sk_D_2) = (X0))
% 8.53/8.75          | ~ (m1_subset_1 @ X0 @ sk_C)
% 8.53/8.75          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A)
% 8.53/8.75          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['134', '163'])).
% 8.53/8.75  thf('165', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (r2_hidden @ (k1_mcart_1 @ sk_E_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['6', '9'])).
% 8.53/8.75  thf('166', plain,
% 8.53/8.75      (![X35 : $i, X36 : $i, X37 : $i]:
% 8.53/8.75         ((r2_hidden @ (k1_mcart_1 @ X35) @ X36)
% 8.53/8.75          | ~ (r2_hidden @ X35 @ (k2_zfmisc_1 @ X36 @ X37)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t10_mcart_1])).
% 8.53/8.75  thf('167', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 8.53/8.75      inference('sup-', [status(thm)], ['165', '166'])).
% 8.53/8.75  thf('168', plain,
% 8.53/8.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['114', '115'])).
% 8.53/8.75  thf('169', plain,
% 8.53/8.75      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A)
% 8.53/8.75        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['167', '168'])).
% 8.53/8.75  thf('170', plain,
% 8.53/8.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 8.53/8.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 8.53/8.75  thf('171', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 8.53/8.75            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 8.53/8.75          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 8.53/8.75      inference('sup+', [status(thm)], ['169', '170'])).
% 8.53/8.75  thf('172', plain,
% 8.53/8.75      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 8.53/8.75      inference('demod', [status(thm)], ['70', '75', '77'])).
% 8.53/8.75  thf('173', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 8.53/8.75      inference('demod', [status(thm)], ['171', '172'])).
% 8.53/8.75  thf('174', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56) != (k1_xboole_0))
% 8.53/8.75          | ((X56) = (k1_xboole_0))
% 8.53/8.75          | ((X55) = (k1_xboole_0))
% 8.53/8.75          | ((X54) = (k1_xboole_0))
% 8.53/8.75          | ((X53) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('175', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_xboole_0) != (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A)
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['173', '174'])).
% 8.53/8.75  thf('176', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 8.53/8.75      inference('simplify', [status(thm)], ['175'])).
% 8.53/8.75  thf('177', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('178', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('179', plain, (((sk_C) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('180', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)],
% 8.53/8.75                ['176', '177', '178', '179'])).
% 8.53/8.75  thf('181', plain,
% 8.53/8.75      (![X22 : $i, X23 : $i]:
% 8.53/8.75         ((m1_subset_1 @ X22 @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 8.53/8.75      inference('clc', [status(thm)], ['22', '23'])).
% 8.53/8.75  thf('182', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 8.53/8.75      inference('sup-', [status(thm)], ['180', '181'])).
% 8.53/8.75  thf('183', plain,
% 8.53/8.75      (![X39 : $i, X40 : $i]: ((k4_tarski @ X39 @ X40) != (X39))),
% 8.53/8.75      inference('demod', [status(thm)], ['1', '2'])).
% 8.53/8.75  thf('184', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_xboole_0) != (X0))
% 8.53/8.75          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A))),
% 8.53/8.75      inference('sup-', [status(thm)], ['182', '183'])).
% 8.53/8.75  thf('185', plain,
% 8.53/8.75      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_3)) @ sk_A)),
% 8.53/8.75      inference('simplify', [status(thm)], ['184'])).
% 8.53/8.75  thf('186', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((sk_E_3) != (k4_tarski @ (k1_mcart_1 @ sk_E_3) @ X0))
% 8.53/8.75          | ((sk_D_2) = (X0))
% 8.53/8.75          | ~ (m1_subset_1 @ X0 @ sk_C)
% 8.53/8.75          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('demod', [status(thm)], ['164', '185'])).
% 8.53/8.75  thf('187', plain,
% 8.53/8.75      ((((sk_E_3) != (sk_E_3))
% 8.53/8.75        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_3) @ sk_C)
% 8.53/8.75        | ((sk_D_2) = (k2_mcart_1 @ sk_E_3)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['105', '186'])).
% 8.53/8.75  thf('188', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (r2_hidden @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['4', '5'])).
% 8.53/8.75  thf('189', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.53/8.75         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 8.53/8.75          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['36', '37'])).
% 8.53/8.75  thf('190', plain,
% 8.53/8.75      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (r2_hidden @ (k2_mcart_1 @ sk_E_3) @ sk_C))),
% 8.53/8.75      inference('sup-', [status(thm)], ['188', '189'])).
% 8.53/8.75  thf('191', plain,
% 8.53/8.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['114', '115'])).
% 8.53/8.75  thf('192', plain,
% 8.53/8.75      (((r2_hidden @ (k2_mcart_1 @ sk_E_3) @ sk_C)
% 8.53/8.75        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['190', '191'])).
% 8.53/8.75  thf('193', plain,
% 8.53/8.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 8.53/8.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 8.53/8.75  thf('194', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 8.53/8.75            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 8.53/8.75          | (r2_hidden @ (k2_mcart_1 @ sk_E_3) @ sk_C))),
% 8.53/8.75      inference('sup+', [status(thm)], ['192', '193'])).
% 8.53/8.75  thf('195', plain,
% 8.53/8.75      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 8.53/8.75      inference('demod', [status(thm)], ['70', '75', '77'])).
% 8.53/8.75  thf('196', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ (k2_mcart_1 @ sk_E_3) @ sk_C))),
% 8.53/8.75      inference('demod', [status(thm)], ['194', '195'])).
% 8.53/8.75  thf('197', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56) != (k1_xboole_0))
% 8.53/8.75          | ((X56) = (k1_xboole_0))
% 8.53/8.75          | ((X55) = (k1_xboole_0))
% 8.53/8.75          | ((X54) = (k1_xboole_0))
% 8.53/8.75          | ((X53) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('198', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_xboole_0) != (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ (k2_mcart_1 @ sk_E_3) @ sk_C)
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((X0) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['196', '197'])).
% 8.53/8.75  thf('199', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0))
% 8.53/8.75          | ((sk_C) = (k1_xboole_0))
% 8.53/8.75          | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75          | ((sk_A) = (k1_xboole_0))
% 8.53/8.75          | (r2_hidden @ (k2_mcart_1 @ sk_E_3) @ sk_C))),
% 8.53/8.75      inference('simplify', [status(thm)], ['198'])).
% 8.53/8.75  thf('200', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('201', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('202', plain, (((sk_C) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('203', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0)) | (r2_hidden @ (k2_mcart_1 @ sk_E_3) @ sk_C))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)],
% 8.53/8.75                ['199', '200', '201', '202'])).
% 8.53/8.75  thf('204', plain,
% 8.53/8.75      (![X22 : $i, X23 : $i]:
% 8.53/8.75         ((m1_subset_1 @ X22 @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 8.53/8.75      inference('clc', [status(thm)], ['22', '23'])).
% 8.53/8.75  thf('205', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (k2_mcart_1 @ sk_E_3) @ sk_C))),
% 8.53/8.75      inference('sup-', [status(thm)], ['203', '204'])).
% 8.53/8.75  thf('206', plain,
% 8.53/8.75      (![X39 : $i, X40 : $i]: ((k4_tarski @ X39 @ X40) != (X39))),
% 8.53/8.75      inference('demod', [status(thm)], ['1', '2'])).
% 8.53/8.75  thf('207', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((k1_xboole_0) != (X0))
% 8.53/8.75          | (m1_subset_1 @ (k2_mcart_1 @ sk_E_3) @ sk_C))),
% 8.53/8.75      inference('sup-', [status(thm)], ['205', '206'])).
% 8.53/8.75  thf('208', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_3) @ sk_C)),
% 8.53/8.75      inference('simplify', [status(thm)], ['207'])).
% 8.53/8.75  thf('209', plain,
% 8.53/8.75      ((((sk_E_3) != (sk_E_3))
% 8.53/8.75        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | ((sk_D_2) = (k2_mcart_1 @ sk_E_3)))),
% 8.53/8.75      inference('demod', [status(thm)], ['187', '208'])).
% 8.53/8.75  thf('210', plain,
% 8.53/8.75      ((((sk_D_2) = (k2_mcart_1 @ sk_E_3))
% 8.53/8.75        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['209'])).
% 8.53/8.75  thf('211', plain,
% 8.53/8.75      (((sk_D_2) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('212', plain,
% 8.53/8.75      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf(t50_mcart_1, axiom,
% 8.53/8.75    (![A:$i,B:$i,C:$i]:
% 8.53/8.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 8.53/8.75          ( ( C ) != ( k1_xboole_0 ) ) & 
% 8.53/8.75          ( ~( ![D:$i]:
% 8.53/8.75               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 8.53/8.75                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 8.53/8.75                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 8.53/8.75                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 8.53/8.75                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 8.53/8.75                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 8.53/8.75  thf('213', plain,
% 8.53/8.75      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 8.53/8.75         (((X49) = (k1_xboole_0))
% 8.53/8.75          | ((X50) = (k1_xboole_0))
% 8.53/8.75          | ((k7_mcart_1 @ X49 @ X50 @ X52 @ X51) = (k2_mcart_1 @ X51))
% 8.53/8.75          | ~ (m1_subset_1 @ X51 @ (k3_zfmisc_1 @ X49 @ X50 @ X52))
% 8.53/8.75          | ((X52) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t50_mcart_1])).
% 8.53/8.75  thf('214', plain,
% 8.53/8.75      ((((sk_C) = (k1_xboole_0))
% 8.53/8.75        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) = (k2_mcart_1 @ sk_E_3))
% 8.53/8.75        | ((sk_B_2) = (k1_xboole_0))
% 8.53/8.75        | ((sk_A) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['212', '213'])).
% 8.53/8.75  thf('215', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('216', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('217', plain, (((sk_C) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('218', plain,
% 8.53/8.75      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_3) = (k2_mcart_1 @ sk_E_3))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)],
% 8.53/8.75                ['214', '215', '216', '217'])).
% 8.53/8.75  thf('219', plain, (((sk_D_2) != (k2_mcart_1 @ sk_E_3))),
% 8.53/8.75      inference('demod', [status(thm)], ['211', '218'])).
% 8.53/8.75  thf('220', plain, ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)], ['210', '219'])).
% 8.53/8.75  thf('221', plain,
% 8.53/8.75      ((m1_subset_1 @ sk_E_3 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('222', plain,
% 8.53/8.75      (![X23 : $i, X24 : $i]:
% 8.53/8.75         (~ (m1_subset_1 @ X24 @ X23)
% 8.53/8.75          | (v1_xboole_0 @ X24)
% 8.53/8.75          | ~ (v1_xboole_0 @ X23))),
% 8.53/8.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.53/8.75  thf('223', plain,
% 8.53/8.75      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 8.53/8.75        | (v1_xboole_0 @ sk_E_3))),
% 8.53/8.75      inference('sup-', [status(thm)], ['221', '222'])).
% 8.53/8.75  thf('224', plain, ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)], ['210', '219'])).
% 8.53/8.75  thf('225', plain, ((v1_xboole_0 @ sk_E_3)),
% 8.53/8.75      inference('demod', [status(thm)], ['223', '224'])).
% 8.53/8.75  thf('226', plain,
% 8.53/8.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['114', '115'])).
% 8.53/8.75  thf('227', plain,
% 8.53/8.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['114', '115'])).
% 8.53/8.75  thf('228', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i]:
% 8.53/8.75         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 8.53/8.75      inference('sup+', [status(thm)], ['226', '227'])).
% 8.53/8.75  thf('229', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_E_3) = (X0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['225', '228'])).
% 8.53/8.75  thf('230', plain, (((sk_E_3) = (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 8.53/8.75      inference('sup-', [status(thm)], ['220', '229'])).
% 8.53/8.75  thf('231', plain,
% 8.53/8.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)
% 8.53/8.75           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X31 @ X32 @ X33) @ X34))),
% 8.53/8.75      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 8.53/8.75  thf('232', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 8.53/8.75           = (k2_zfmisc_1 @ sk_E_3 @ X0))),
% 8.53/8.75      inference('sup+', [status(thm)], ['230', '231'])).
% 8.53/8.75  thf('233', plain,
% 8.53/8.75      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 8.53/8.75      inference('demod', [status(thm)], ['70', '75', '77'])).
% 8.53/8.75  thf('234', plain, ((v1_xboole_0 @ sk_E_3)),
% 8.53/8.75      inference('demod', [status(thm)], ['223', '224'])).
% 8.53/8.75  thf('235', plain,
% 8.53/8.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['114', '115'])).
% 8.53/8.75  thf('236', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('237', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('238', plain, (![X1 : $i]: ((sk_E_3) = (k2_zfmisc_1 @ sk_E_3 @ X1))),
% 8.53/8.75      inference('demod', [status(thm)], ['233', '236', '237'])).
% 8.53/8.75  thf('239', plain,
% 8.53/8.75      (![X0 : $i]: ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (sk_E_3))),
% 8.53/8.75      inference('demod', [status(thm)], ['232', '238'])).
% 8.53/8.75  thf('240', plain,
% 8.53/8.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['114', '115'])).
% 8.53/8.75  thf('241', plain,
% 8.53/8.75      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X53 @ X54 @ X55 @ X56) != (k1_xboole_0))
% 8.53/8.75          | ((X56) = (k1_xboole_0))
% 8.53/8.75          | ((X55) = (k1_xboole_0))
% 8.53/8.75          | ((X54) = (k1_xboole_0))
% 8.53/8.75          | ((X53) = (k1_xboole_0)))),
% 8.53/8.75      inference('cnf', [status(esa)], [t55_mcart_1])).
% 8.53/8.75  thf('242', plain,
% 8.53/8.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.53/8.75         (((k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1) != (X0))
% 8.53/8.75          | ~ (v1_xboole_0 @ X0)
% 8.53/8.75          | ((X4) = (k1_xboole_0))
% 8.53/8.75          | ((X3) = (k1_xboole_0))
% 8.53/8.75          | ((X2) = (k1_xboole_0))
% 8.53/8.75          | ((X1) = (k1_xboole_0)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['240', '241'])).
% 8.53/8.75  thf('243', plain,
% 8.53/8.75      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.53/8.75         (((X1) = (k1_xboole_0))
% 8.53/8.75          | ((X2) = (k1_xboole_0))
% 8.53/8.75          | ((X3) = (k1_xboole_0))
% 8.53/8.75          | ((X4) = (k1_xboole_0))
% 8.53/8.75          | ~ (v1_xboole_0 @ (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1)))),
% 8.53/8.75      inference('simplify', [status(thm)], ['242'])).
% 8.53/8.75  thf('244', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('245', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('246', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('247', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('248', plain,
% 8.53/8.75      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.53/8.75         (((X1) = (sk_E_3))
% 8.53/8.75          | ((X2) = (sk_E_3))
% 8.53/8.75          | ((X3) = (sk_E_3))
% 8.53/8.75          | ((X4) = (sk_E_3))
% 8.53/8.75          | ~ (v1_xboole_0 @ (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1)))),
% 8.53/8.75      inference('demod', [status(thm)], ['243', '244', '245', '246', '247'])).
% 8.53/8.75  thf('249', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (~ (v1_xboole_0 @ sk_E_3)
% 8.53/8.75          | ((sk_A) = (sk_E_3))
% 8.53/8.75          | ((sk_B_2) = (sk_E_3))
% 8.53/8.75          | ((sk_C) = (sk_E_3))
% 8.53/8.75          | ((X0) = (sk_E_3)))),
% 8.53/8.75      inference('sup-', [status(thm)], ['239', '248'])).
% 8.53/8.75  thf('250', plain, ((v1_xboole_0 @ sk_E_3)),
% 8.53/8.75      inference('demod', [status(thm)], ['223', '224'])).
% 8.53/8.75  thf('251', plain,
% 8.53/8.75      (![X0 : $i]:
% 8.53/8.75         (((sk_A) = (sk_E_3))
% 8.53/8.75          | ((sk_B_2) = (sk_E_3))
% 8.53/8.75          | ((sk_C) = (sk_E_3))
% 8.53/8.75          | ((X0) = (sk_E_3)))),
% 8.53/8.75      inference('demod', [status(thm)], ['249', '250'])).
% 8.53/8.75  thf('252', plain, (((sk_C) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('253', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('254', plain, (((sk_C) != (sk_E_3))),
% 8.53/8.75      inference('demod', [status(thm)], ['252', '253'])).
% 8.53/8.75  thf('255', plain, (((sk_B_2) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('256', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('257', plain, (((sk_B_2) != (sk_E_3))),
% 8.53/8.75      inference('demod', [status(thm)], ['255', '256'])).
% 8.53/8.75  thf('258', plain, (((sk_A) != (k1_xboole_0))),
% 8.53/8.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.75  thf('259', plain, (((sk_E_3) = (k1_xboole_0))),
% 8.53/8.75      inference('sup-', [status(thm)], ['234', '235'])).
% 8.53/8.75  thf('260', plain, (((sk_A) != (sk_E_3))),
% 8.53/8.75      inference('demod', [status(thm)], ['258', '259'])).
% 8.53/8.75  thf('261', plain, (![X0 : $i]: ((X0) = (sk_E_3))),
% 8.53/8.75      inference('simplify_reflect-', [status(thm)],
% 8.53/8.75                ['251', '254', '257', '260'])).
% 8.53/8.75  thf('262', plain, (![X39 : $i]: ((sk_E_3) != (X39))),
% 8.53/8.75      inference('demod', [status(thm)], ['3', '261'])).
% 8.53/8.75  thf('263', plain, ($false), inference('simplify', [status(thm)], ['262'])).
% 8.53/8.75  
% 8.53/8.75  % SZS output end Refutation
% 8.53/8.75  
% 8.53/8.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
