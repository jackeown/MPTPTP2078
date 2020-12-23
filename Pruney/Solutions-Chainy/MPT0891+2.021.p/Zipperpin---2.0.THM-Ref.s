%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X2kgf4uXAI

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:36 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 464 expanded)
%              Number of leaves         :   29 ( 147 expanded)
%              Depth                    :   16
%              Number of atoms          : 1100 (7592 expanded)
%              Number of equality atoms :  148 (1064 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

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

thf('0',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X14 @ X16 ) @ X15 )
       != ( k2_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X9 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('17',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(clc,[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['16'])).

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

thf('21',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    m1_subset_1 @ sk_D_2 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('26',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X34
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X31 @ X32 @ X33 @ X34 ) @ ( k6_mcart_1 @ X31 @ X32 @ X33 @ X34 ) @ ( k7_mcart_1 @ X31 @ X32 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X31 @ X32 @ X33 ) )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X34
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X31 @ X32 @ X33 @ X34 ) @ ( k6_mcart_1 @ X31 @ X32 @ X33 @ X34 ) @ ( k7_mcart_1 @ X31 @ X32 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ X33 ) )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('36',plain,(
    ! [X35: $i,X37: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X35 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_mcart_1 @ sk_D_2 )
    = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X29 @ X27 )
      | ( ( sk_B @ X27 )
       != ( k3_mcart_1 @ X29 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_2 )
      | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
         != sk_D_2 )
        | ( ( k2_tarski @ sk_D_2 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['20','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
       != sk_D_2 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_D_2 )
        | ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
          = sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','45'])).

thf('47',plain,
    ( ( ( sk_B @ ( k2_tarski @ sk_D_2 @ sk_D_2 ) )
      = sk_D_2 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
       != sk_D_2 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('49',plain,
    ( $false
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('51',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('52',plain,
    ( ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
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

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k2_mcart_1 @ X24 ) )
      | ( X24
       != ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('55',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != ( k2_mcart_1 @ ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X35: $i,X37: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X35 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('57',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != X26 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(clc,[status(thm)],['3','18'])).

thf('61',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('62',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('63',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('64',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ( ( sk_B @ X27 )
       != ( k3_mcart_1 @ X29 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_2 )
      | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
         != sk_D_2 )
        | ( ( k2_tarski @ sk_D_2 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
       != sk_D_2 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_D_2 )
        | ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
          = sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,
    ( ( ( sk_B @ ( k2_tarski @ sk_D_2 @ sk_D_2 ) )
      = sk_D_2 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
       != sk_D_2 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('73',plain,(
    sk_D_2
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('75',plain,
    ( sk_D_2
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['59','73','74'])).

thf('76',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['49','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X2kgf4uXAI
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 228 iterations in 0.129s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.58  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.36/0.58  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.58  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.36/0.58  thf(t29_mcart_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.58          ( ![B:$i]:
% 0.36/0.58            ( ~( ( r2_hidden @ B @ A ) & 
% 0.36/0.58                 ( ![C:$i,D:$i,E:$i]:
% 0.36/0.58                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.36/0.58                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      (![X27 : $i]:
% 0.36/0.58         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.36/0.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.36/0.58  thf(d2_tarski, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.36/0.58       ( ![D:$i]:
% 0.36/0.58         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X10 @ X8)
% 0.36/0.58          | ((X10) = (X9))
% 0.36/0.58          | ((X10) = (X6))
% 0.36/0.58          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d2_tarski])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (![X6 : $i, X9 : $i, X10 : $i]:
% 0.36/0.58         (((X10) = (X6))
% 0.36/0.58          | ((X10) = (X9))
% 0.36/0.58          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.36/0.58          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.36/0.58          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '2'])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (![X27 : $i]:
% 0.36/0.58         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.36/0.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.36/0.58  thf(d5_xboole_0, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.58       ( ![D:$i]:
% 0.36/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.58          | (r2_hidden @ X4 @ X1)
% 0.36/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.36/0.58          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (![X27 : $i]:
% 0.36/0.58         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.36/0.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.58          | ~ (r2_hidden @ X4 @ X2)
% 0.36/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X4 @ X2)
% 0.36/0.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.36/0.58          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['8', '10'])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.36/0.58          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['7', '11'])).
% 0.36/0.58  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.58  thf(t72_zfmisc_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.36/0.58       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X14 @ X15)
% 0.36/0.58          | ((k4_xboole_0 @ (k2_tarski @ X14 @ X16) @ X15)
% 0.36/0.58              != (k2_tarski @ X14 @ X16)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.36/0.58          | ~ (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.58         (((X7) != (X9))
% 0.36/0.58          | (r2_hidden @ X7 @ X8)
% 0.36/0.58          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d2_tarski])).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      (![X6 : $i, X9 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X9 @ X6))),
% 0.36/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['15', '17'])).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((sk_B @ (k2_tarski @ X1 @ X0)) = (X0))
% 0.36/0.58          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 0.36/0.58      inference('clc', [status(thm)], ['3', '18'])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (![X6 : $i, X9 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X9 @ X6))),
% 0.36/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.58  thf(t51_mcart_1, conjecture,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.58          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.36/0.58          ( ~( ![D:$i]:
% 0.36/0.58               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.36/0.58                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.36/0.58                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.36/0.58                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.58        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.58             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.36/0.58             ( ~( ![D:$i]:
% 0.36/0.58                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.36/0.58                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.36/0.58                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.36/0.58                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 0.36/0.58        | ((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 0.36/0.58        | ((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('split', [status(esa)], ['21'])).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(d3_zfmisc_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.36/0.58       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.58         ((k3_zfmisc_1 @ X21 @ X22 @ X23)
% 0.36/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_D_2 @ 
% 0.36/0.58        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.36/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.58  thf(t48_mcart_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.58          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.36/0.58          ( ~( ![D:$i]:
% 0.36/0.58               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.36/0.58                 ( ( D ) =
% 0.36/0.58                   ( k3_mcart_1 @
% 0.36/0.58                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.36/0.58                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.36/0.58                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.58         (((X31) = (k1_xboole_0))
% 0.36/0.58          | ((X32) = (k1_xboole_0))
% 0.36/0.58          | ((X34)
% 0.36/0.58              = (k3_mcart_1 @ (k5_mcart_1 @ X31 @ X32 @ X33 @ X34) @ 
% 0.36/0.58                 (k6_mcart_1 @ X31 @ X32 @ X33 @ X34) @ 
% 0.36/0.58                 (k7_mcart_1 @ X31 @ X32 @ X33 @ X34)))
% 0.36/0.58          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X31 @ X32 @ X33))
% 0.36/0.58          | ((X33) = (k1_xboole_0)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.58         ((k3_zfmisc_1 @ X21 @ X22 @ X23)
% 0.36/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.58         (((X31) = (k1_xboole_0))
% 0.36/0.58          | ((X32) = (k1_xboole_0))
% 0.36/0.58          | ((X34)
% 0.36/0.58              = (k3_mcart_1 @ (k5_mcart_1 @ X31 @ X32 @ X33 @ X34) @ 
% 0.36/0.58                 (k6_mcart_1 @ X31 @ X32 @ X33 @ X34) @ 
% 0.36/0.58                 (k7_mcart_1 @ X31 @ X32 @ X33 @ X34)))
% 0.36/0.58          | ~ (m1_subset_1 @ X34 @ 
% 0.36/0.58               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32) @ X33))
% 0.36/0.58          | ((X33) = (k1_xboole_0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      ((((sk_C) = (k1_xboole_0))
% 0.36/0.58        | ((sk_D_2)
% 0.36/0.58            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.36/0.58        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['25', '28'])).
% 0.36/0.58  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('31', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (((sk_D_2)
% 0.36/0.58         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (((sk_D_2)
% 0.36/0.58         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.36/0.58  thf(d3_mcart_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.58         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 0.36/0.58           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.36/0.58  thf(t7_mcart_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.36/0.58       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      (![X35 : $i, X37 : $i]: ((k2_mcart_1 @ (k4_tarski @ X35 @ X37)) = (X37))),
% 0.36/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (((k2_mcart_1 @ sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))),
% 0.36/0.58      inference('sup+', [status(thm)], ['34', '37'])).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      (((sk_D_2)
% 0.36/0.58         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k2_mcart_1 @ sk_D_2)))),
% 0.36/0.58      inference('demod', [status(thm)], ['33', '38'])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.58         (((X27) = (k1_xboole_0))
% 0.36/0.58          | ~ (r2_hidden @ X29 @ X27)
% 0.36/0.58          | ((sk_B @ X27) != (k3_mcart_1 @ X29 @ X28 @ X30)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((sk_B @ X0) != (sk_D_2))
% 0.36/0.58          | ~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ X0)
% 0.36/0.58          | ((X0) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (~ (r2_hidden @ sk_D_2 @ X0)
% 0.36/0.58           | ((X0) = (k1_xboole_0))
% 0.36/0.58           | ((sk_B @ X0) != (sk_D_2))))
% 0.36/0.58         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['22', '41'])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2))
% 0.36/0.58           | ((k2_tarski @ sk_D_2 @ X0) = (k1_xboole_0))))
% 0.36/0.58         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['20', '42'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['15', '17'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      ((![X0 : $i]: ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('clc', [status(thm)], ['43', '44'])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (((X0) != (sk_D_2)) | ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) = (sk_D_2))))
% 0.36/0.58         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['19', '45'])).
% 0.36/0.58  thf('47', plain,
% 0.36/0.58      ((((sk_B @ (k2_tarski @ sk_D_2 @ sk_D_2)) = (sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      ((![X0 : $i]: ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('clc', [status(thm)], ['43', '44'])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (($false)
% 0.36/0.58         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('split', [status(esa)], ['21'])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      (((sk_D_2)
% 0.36/0.58         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.36/0.58  thf('52', plain,
% 0.36/0.58      ((((sk_D_2)
% 0.36/0.58          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.36/0.58  thf('53', plain,
% 0.36/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.58         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 0.36/0.58           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.36/0.58  thf(t20_mcart_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.36/0.58       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.36/0.58  thf('54', plain,
% 0.36/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.58         (((X24) != (k2_mcart_1 @ X24)) | ((X24) != (k4_tarski @ X25 @ X26)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.36/0.58  thf('55', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i]:
% 0.36/0.58         ((k4_tarski @ X25 @ X26) != (k2_mcart_1 @ (k4_tarski @ X25 @ X26)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['54'])).
% 0.36/0.58  thf('56', plain,
% 0.36/0.58      (![X35 : $i, X37 : $i]: ((k2_mcart_1 @ (k4_tarski @ X35 @ X37)) = (X37))),
% 0.36/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.36/0.58  thf('57', plain, (![X25 : $i, X26 : $i]: ((k4_tarski @ X25 @ X26) != (X26))),
% 0.36/0.58      inference('demod', [status(thm)], ['55', '56'])).
% 0.36/0.58  thf('58', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['53', '57'])).
% 0.36/0.58  thf('59', plain,
% 0.36/0.58      (~ (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['52', '58'])).
% 0.36/0.58  thf('60', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((sk_B @ (k2_tarski @ X1 @ X0)) = (X0))
% 0.36/0.58          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 0.36/0.58      inference('clc', [status(thm)], ['3', '18'])).
% 0.36/0.58  thf('61', plain,
% 0.36/0.58      (![X6 : $i, X9 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X9 @ X6))),
% 0.36/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.58  thf('62', plain,
% 0.36/0.58      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('split', [status(esa)], ['21'])).
% 0.36/0.58  thf('63', plain,
% 0.36/0.58      (((sk_D_2)
% 0.36/0.58         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.36/0.58            (k2_mcart_1 @ sk_D_2)))),
% 0.36/0.58      inference('demod', [status(thm)], ['33', '38'])).
% 0.36/0.58  thf('64', plain,
% 0.36/0.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.58         (((X27) = (k1_xboole_0))
% 0.36/0.58          | ~ (r2_hidden @ X28 @ X27)
% 0.36/0.58          | ((sk_B @ X27) != (k3_mcart_1 @ X29 @ X28 @ X30)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.36/0.58  thf('65', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((sk_B @ X0) != (sk_D_2))
% 0.36/0.58          | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ X0)
% 0.36/0.58          | ((X0) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.58  thf('66', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (~ (r2_hidden @ sk_D_2 @ X0)
% 0.36/0.58           | ((X0) = (k1_xboole_0))
% 0.36/0.58           | ((sk_B @ X0) != (sk_D_2))))
% 0.36/0.58         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['62', '65'])).
% 0.36/0.58  thf('67', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2))
% 0.36/0.58           | ((k2_tarski @ sk_D_2 @ X0) = (k1_xboole_0))))
% 0.36/0.58         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['61', '66'])).
% 0.36/0.58  thf('68', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['15', '17'])).
% 0.36/0.58  thf('69', plain,
% 0.36/0.58      ((![X0 : $i]: ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('clc', [status(thm)], ['67', '68'])).
% 0.36/0.58  thf('70', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (((X0) != (sk_D_2)) | ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) = (sk_D_2))))
% 0.36/0.58         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['60', '69'])).
% 0.36/0.58  thf('71', plain,
% 0.36/0.58      ((((sk_B @ (k2_tarski @ sk_D_2 @ sk_D_2)) = (sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('simplify', [status(thm)], ['70'])).
% 0.36/0.58  thf('72', plain,
% 0.36/0.58      ((![X0 : $i]: ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2)))
% 0.36/0.58         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.36/0.58      inference('clc', [status(thm)], ['67', '68'])).
% 0.36/0.58  thf('73', plain,
% 0.36/0.58      (~ (((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.36/0.58  thf('74', plain,
% 0.36/0.58      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))) | 
% 0.36/0.58       (((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))) | 
% 0.36/0.58       (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.36/0.58      inference('split', [status(esa)], ['21'])).
% 0.36/0.58  thf('75', plain,
% 0.36/0.58      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['59', '73', '74'])).
% 0.36/0.58  thf('76', plain, ($false),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['49', '75'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
