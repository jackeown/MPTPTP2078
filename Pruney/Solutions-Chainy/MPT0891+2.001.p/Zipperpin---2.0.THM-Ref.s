%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U0kFqHWtzA

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 190 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  869 (3131 expanded)
%              Number of equality atoms :  118 ( 484 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_3_type,type,(
    sk_A_3: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( X44
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X41 @ X42 @ X43 @ X44 ) @ ( k6_mcart_1 @ X41 @ X42 @ X43 @ X44 ) @ ( k7_mcart_1 @ X41 @ X42 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k3_zfmisc_1 @ X41 @ X42 @ X43 ) )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_mcart_1 @ X19 @ X20 @ X21 )
      = ( k4_tarski @ ( k4_tarski @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('9',plain,(
    ! [X49: $i,X51: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X49 @ X51 ) )
      = X51 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_mcart_1 @ sk_D )
    = ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['13'])).

thf('16',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('17',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_mcart_1 @ X19 @ X20 @ X21 )
      = ( k4_tarski @ ( k4_tarski @ X19 @ X20 ) @ X21 ) ) ),
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

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k2_mcart_1 @ X34 ) )
      | ( X34
       != ( k4_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('20',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k4_tarski @ X35 @ X36 )
     != ( k2_mcart_1 @ ( k4_tarski @ X35 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X49: $i,X51: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X49 @ X51 ) )
      = X51 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('22',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k4_tarski @ X35 @ X36 )
     != X36 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['13'])).

thf('26',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('27',plain,(
    ! [X37: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X37 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X37 )
      | ( ( sk_B_1 @ X37 )
       != ( k3_mcart_1 @ X39 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','43'])).

thf('45',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['13'])).

thf('46',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['24','44','45'])).

thf('47',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['14','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 ) ),
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

thf('49',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X45 @ X46 @ X48 @ X47 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k3_zfmisc_1 @ X45 @ X46 @ X48 ) )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('50',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_D @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','47','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

thf('57',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( r2_hidden @ X39 @ X37 )
      | ( ( sk_B_1 @ X37 )
       != ( k3_mcart_1 @ X39 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('61',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U0kFqHWtzA
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:37:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 116 iterations in 0.050s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.50  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_A_3_type, type, sk_A_3: $i).
% 0.20/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(t51_mcart_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ~( ![D:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.50                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.50                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.50                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50             ( ~( ![D:$i]:
% 0.20/0.50                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.50                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.50                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.50                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A_3 @ sk_B_2 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t48_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ~( ![D:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.50                 ( ( D ) =
% 0.20/0.50                   ( k3_mcart_1 @
% 0.20/0.50                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.50                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.50                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.20/0.50         (((X41) = (k1_xboole_0))
% 0.20/0.50          | ((X42) = (k1_xboole_0))
% 0.20/0.50          | ((X44)
% 0.20/0.50              = (k3_mcart_1 @ (k5_mcart_1 @ X41 @ X42 @ X43 @ X44) @ 
% 0.20/0.50                 (k6_mcart_1 @ X41 @ X42 @ X43 @ X44) @ 
% 0.20/0.50                 (k7_mcart_1 @ X41 @ X42 @ X43 @ X44)))
% 0.20/0.50          | ~ (m1_subset_1 @ X44 @ (k3_zfmisc_1 @ X41 @ X42 @ X43))
% 0.20/0.50          | ((X43) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_D)
% 0.20/0.50            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50               (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50               (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))
% 0.20/0.50        | ((sk_B_2) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A_3) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain, (((sk_A_3) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (((sk_D)
% 0.20/0.50         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((sk_D)
% 0.20/0.50         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.50  thf(d3_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         ((k3_mcart_1 @ X19 @ X20 @ X21)
% 0.20/0.50           = (k4_tarski @ (k4_tarski @ X19 @ X20) @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.50  thf(t7_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X49 : $i, X51 : $i]: ((k2_mcart_1 @ (k4_tarski @ X49 @ X51)) = (X51))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (((k2_mcart_1 @ sk_D) = (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))),
% 0.20/0.50      inference('sup+', [status(thm)], ['7', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((sk_D)
% 0.20/0.50         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k2_mcart_1 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((((sk_D) = (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))
% 0.20/0.50        | ((sk_D) = (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))
% 0.20/0.50        | ((sk_D) = (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((((sk_D) = (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))
% 0.20/0.50         <= ((((sk_D) = (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((sk_D) = (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))
% 0.20/0.50         <= ((((sk_D) = (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['13'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((sk_D)
% 0.20/0.50         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((((sk_D)
% 0.20/0.50          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50             (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ sk_D)))
% 0.20/0.50         <= ((((sk_D) = (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         ((k3_mcart_1 @ X19 @ X20 @ X21)
% 0.20/0.50           = (k4_tarski @ (k4_tarski @ X19 @ X20) @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.50  thf(t20_mcart_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.50         (((X34) != (k2_mcart_1 @ X34)) | ((X34) != (k4_tarski @ X35 @ X36)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i]:
% 0.20/0.50         ((k4_tarski @ X35 @ X36) != (k2_mcart_1 @ (k4_tarski @ X35 @ X36)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X49 : $i, X51 : $i]: ((k2_mcart_1 @ (k4_tarski @ X49 @ X51)) = (X51))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('22', plain, (![X35 : $i, X36 : $i]: ((k4_tarski @ X35 @ X36) != (X36))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (~ (((sk_D) = (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['17', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((sk_D) = (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))
% 0.20/0.50         <= ((((sk_D) = (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['13'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((sk_D)
% 0.20/0.50         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50            (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.50  thf(t29_mcart_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.50                 ( ![C:$i,D:$i,E:$i]:
% 0.20/0.50                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.50                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X37 : $i]:
% 0.20/0.50         (((X37) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X37) @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.50  thf(d1_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X3 : $i, X6 : $i]:
% 0.20/0.50         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.50          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.50  thf(t1_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.50  thf(t49_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.50  thf('33', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, (![X0 : $i]: ((sk_B_1 @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.50         (((X37) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X38 @ X37)
% 0.20/0.50          | ((sk_B_1 @ X37) != (k3_mcart_1 @ X39 @ X38 @ X40)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.20/0.50          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.20/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.50  thf('38', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (~ (r2_hidden @ (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D) @ 
% 0.20/0.50          (k1_tarski @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D)))
% 0.20/0.50         <= ((((sk_D) = (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('43', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.20/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (~ (((sk_D) = (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((((sk_D) = (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))) | 
% 0.20/0.50       (((sk_D) = (k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))) | 
% 0.20/0.50       (((sk_D) = (k7_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['13'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((((sk_D) = (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['24', '44', '45'])).
% 0.20/0.50  thf('47', plain, (((sk_D) = (k5_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['14', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A_3 @ sk_B_2 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t50_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ~( ![D:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.50                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.50                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.50                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.50                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.20/0.50         (((X45) = (k1_xboole_0))
% 0.20/0.50          | ((X46) = (k1_xboole_0))
% 0.20/0.50          | ((k6_mcart_1 @ X45 @ X46 @ X48 @ X47)
% 0.20/0.50              = (k2_mcart_1 @ (k1_mcart_1 @ X47)))
% 0.20/0.50          | ~ (m1_subset_1 @ X47 @ (k3_zfmisc_1 @ X45 @ X46 @ X48))
% 0.20/0.50          | ((X48) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.50        | ((k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)
% 0.20/0.50            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.20/0.50        | ((sk_B_2) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A_3) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain, (((sk_A_3) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('52', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (((k6_mcart_1 @ sk_A_3 @ sk_B_2 @ sk_C_1 @ sk_D)
% 0.20/0.50         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['50', '51', '52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (((sk_D)
% 0.20/0.50         = (k3_mcart_1 @ sk_D @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.20/0.50            (k2_mcart_1 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '47', '54'])).
% 0.20/0.50  thf('56', plain, (![X0 : $i]: ((sk_B_1 @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.50         (((X37) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X39 @ X37)
% 0.20/0.50          | ((sk_B_1 @ X37) != (k3_mcart_1 @ X39 @ X38 @ X40)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.20/0.50          | ~ (r2_hidden @ X3 @ (k1_tarski @ X0))
% 0.20/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.50  thf('60', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain, (~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['55', '61'])).
% 0.20/0.50  thf('63', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.20/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.50  thf('64', plain, ($false), inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
