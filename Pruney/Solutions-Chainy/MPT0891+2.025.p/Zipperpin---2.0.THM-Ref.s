%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jzXFj460j2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 222 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  918 (3893 expanded)
%              Number of equality atoms :  132 ( 604 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
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
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
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

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X29
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X26 @ X27 @ X28 @ X29 ) @ ( k6_mcart_1 @ X26 @ X27 @ X28 @ X29 ) @ ( k7_mcart_1 @ X26 @ X27 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X26 @ X27 @ X28 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('12',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('19',plain,(
    ! [X30: $i,X32: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X30 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_mcart_1 @ sk_D_1 )
    = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ sk_D_1 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k3_mcart_1 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_1 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_1 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_1 ) )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,
    ( ( ( sk_D_1 != sk_D_1 )
      | ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,
    ( ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( k2_mcart_1 @ sk_D_1 )
    = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('30',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('31',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('33',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
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

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19
       != ( k2_mcart_1 @ X19 ) )
      | ( X19
       != ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_tarski @ X20 @ X21 )
     != ( k2_mcart_1 @ ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X30: $i,X32: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X30 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_tarski @ X20 @ X21 )
     != X21 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('42',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('43',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k3_mcart_1 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_1 ) )
         != sk_D_1 )
        | ( ( k2_tarski @ X0 @ sk_D_1 )
          = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( ( sk_D_1 != sk_D_1 )
      | ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,
    ( ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('52',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_D_1
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('59',plain,
    ( sk_D_1
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['40','57','58'])).

thf('60',plain,
    ( ( k2_tarski @ sk_D_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','59'])).

thf('61',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('62',plain,(
    r2_hidden @ sk_D_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('64',plain,(
    $false ),
    inference('sup-',[status(thm)],['62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jzXFj460j2
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 138 iterations in 0.066s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.51  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.51  thf(t29_mcart_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.51                 ( ![C:$i,D:$i,E:$i]:
% 0.21/0.51                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.51                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X22 : $i]:
% 0.21/0.51         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.51  thf(d2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.51          | ((X4) = (X3))
% 0.21/0.51          | ((X4) = (X0))
% 0.21/0.51          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (((X4) = (X0))
% 0.21/0.51          | ((X4) = (X3))
% 0.21/0.51          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.51          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.21/0.51          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X0) != (X1))
% 0.21/0.51          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.21/0.51          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 0.21/0.51      inference('eq_fact', [status(thm)], ['3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X1 : $i]:
% 0.21/0.51         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.21/0.51          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (((X1) != (X0))
% 0.21/0.51          | (r2_hidden @ X1 @ X2)
% 0.21/0.51          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.51  thf(t51_mcart_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ~( ![D:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.51                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.51                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.51                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51             ( ~( ![D:$i]:
% 0.21/0.51                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.51                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.51                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.51                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.21/0.51        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.21/0.51        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.21/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t48_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ~( ![D:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.51                 ( ( D ) =
% 0.21/0.51                   ( k3_mcart_1 @
% 0.21/0.51                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.51                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.51                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.51         (((X26) = (k1_xboole_0))
% 0.21/0.51          | ((X27) = (k1_xboole_0))
% 0.21/0.51          | ((X29)
% 0.21/0.51              = (k3_mcart_1 @ (k5_mcart_1 @ X26 @ X27 @ X28 @ X29) @ 
% 0.21/0.51                 (k6_mcart_1 @ X26 @ X27 @ X28 @ X29) @ 
% 0.21/0.51                 (k7_mcart_1 @ X26 @ X27 @ X28 @ X29)))
% 0.21/0.51          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X26 @ X27 @ X28))
% 0.21/0.51          | ((X28) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((((sk_C) = (k1_xboole_0))
% 0.21/0.51        | ((sk_D_1)
% 0.21/0.51            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.21/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((sk_D_1)
% 0.21/0.51         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((sk_D_1)
% 0.21/0.51         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.51  thf(d3_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.51  thf(t7_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.51       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X30 : $i, X32 : $i]: ((k2_mcart_1 @ (k4_tarski @ X30 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((k2_mcart_1 @ sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['17', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (((sk_D_1)
% 0.21/0.51         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k2_mcart_1 @ sk_D_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((((sk_D_1)
% 0.21/0.51          = (k3_mcart_1 @ sk_D_1 @ 
% 0.21/0.51             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51             (k2_mcart_1 @ sk_D_1))))
% 0.21/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.51         (((X22) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X24 @ X22)
% 0.21/0.51          | ((sk_B @ X22) != (k3_mcart_1 @ X24 @ X23 @ X25)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((sk_B @ X0) != (sk_D_1))
% 0.21/0.51           | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.21/0.51           | ((X0) = (k1_xboole_0))))
% 0.21/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((k2_tarski @ X0 @ sk_D_1) = (k1_xboole_0))
% 0.21/0.51           | ((sk_B @ (k2_tarski @ X0 @ sk_D_1)) != (sk_D_1))))
% 0.21/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((((sk_D_1) != (sk_D_1))
% 0.21/0.51         | ((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))
% 0.21/0.51         | ((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))))
% 0.21/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((k2_mcart_1 @ sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['17', '20'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.21/0.51         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((((sk_D_1) = (k2_mcart_1 @ sk_D_1)))
% 0.21/0.51         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((sk_D_1)
% 0.21/0.51         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k2_mcart_1 @ sk_D_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '21'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((((sk_D_1)
% 0.21/0.51          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ sk_D_1)))
% 0.21/0.51         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.51  thf(t20_mcart_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.51       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (((X19) != (k2_mcart_1 @ X19)) | ((X19) != (k4_tarski @ X20 @ X21)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         ((k4_tarski @ X20 @ X21) != (k2_mcart_1 @ (k4_tarski @ X20 @ X21)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X30 : $i, X32 : $i]: ((k2_mcart_1 @ (k4_tarski @ X30 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('38', plain, (![X20 : $i, X21 : $i]: ((k4_tarski @ X20 @ X21) != (X21))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['33', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X1 : $i]:
% 0.21/0.51         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.21/0.51          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.21/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((sk_D_1)
% 0.21/0.51         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.21/0.51            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.51         (((X22) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X23 @ X22)
% 0.21/0.51          | ((sk_B @ X22) != (k3_mcart_1 @ X24 @ X23 @ X25)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_B @ X0) != (sk_D_1))
% 0.21/0.51          | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ X0)
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (r2_hidden @ sk_D_1 @ X0)
% 0.21/0.51           | ((X0) = (k1_xboole_0))
% 0.21/0.51           | ((sk_B @ X0) != (sk_D_1))))
% 0.21/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((sk_B @ (k2_tarski @ X0 @ sk_D_1)) != (sk_D_1))
% 0.21/0.51           | ((k2_tarski @ X0 @ sk_D_1) = (k1_xboole_0))))
% 0.21/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((((sk_D_1) != (sk_D_1))
% 0.21/0.51         | ((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))
% 0.21/0.51         | ((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))))
% 0.21/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      ((((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (((r2_hidden @ sk_D_1 @ k1_xboole_0))
% 0.21/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf(t113_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.51  thf(t152_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.51  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (~ (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.21/0.51       (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.21/0.51       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('split', [status(esa)], ['8'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['40', '57', '58'])).
% 0.21/0.51  thf('60', plain, (((k2_tarski @ sk_D_1 @ sk_D_1) = (k1_xboole_0))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['28', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.51  thf('62', plain, ((r2_hidden @ sk_D_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.51  thf('63', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('64', plain, ($false), inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
