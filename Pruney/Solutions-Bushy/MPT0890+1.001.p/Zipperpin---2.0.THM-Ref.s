%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0890+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WlWpR7lmly

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 224 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  657 (4636 expanded)
%              Number of equality atoms :   87 ( 670 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t50_mcart_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
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
                    = ( k2_mcart_1 @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_2 ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X20
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X17 @ X18 @ X19 @ X20 ) @ ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) @ ( k7_mcart_1 @ X17 @ X18 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ) )
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
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_mcart_1 @ X14 @ X15 @ X16 )
      = ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(d2_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k2_mcart_1 @ X8 ) )
      | ( X11 = X12 )
      | ( X8
       != ( k4_tarski @ X13 @ X12 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_mcart_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ X13 @ X12 )
       != ( k4_tarski @ X9 @ X10 ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X12 ) )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_D_2 )
    = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_mcart_1 @ X14 @ X15 @ X16 )
      = ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(d1_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k1_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = C ) ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4
       != ( k1_mcart_1 @ X1 ) )
      | ( X4 = X5 )
      | ( X1
       != ( k4_tarski @ X5 @ X6 ) )
      | ( X1
       != ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('17',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ X5 @ X6 )
       != ( k4_tarski @ X2 @ X3 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k1_mcart_1 @ sk_D_2 )
    = ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k1_mcart_1 @ sk_D_2 )
    = ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['17'])).

thf('23',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) )
    = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_mcart_1 @ sk_D_2 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('26',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) )
    = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
   <= ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( k2_mcart_1 @ sk_D_2 )
    = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('30',plain,
    ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ sk_D_2 ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('31',plain,
    ( ( ( k2_mcart_1 @ sk_D_2 )
     != ( k2_mcart_1 @ sk_D_2 ) )
   <= ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_mcart_1 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) )
    = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('34',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('35',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
   <= ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
     != ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('38',plain,(
    ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['32','36','37'])).

thf('39',plain,(
    ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['28','38'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','39'])).


%------------------------------------------------------------------------------
