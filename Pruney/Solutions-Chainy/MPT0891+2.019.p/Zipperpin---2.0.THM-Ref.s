%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3tzu6GzLKT

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:35 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 758 expanded)
%              Number of leaves         :   31 ( 227 expanded)
%              Depth                    :   25
%              Number of atoms          : 1546 (14568 expanded)
%              Number of equality atoms :  212 (2230 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X36 ) @ X36 ) ) ),
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
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X43
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k6_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k7_mcart_1 @ X40 @ X41 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('12',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) )
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
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('19',plain,(
    ! [X44: $i,X46: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X44 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_mcart_1 @ sk_D_2 )
    = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_2 )
      | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_2 ) )
         != sk_D_2 )
        | ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,
    ( ( ( sk_D_2 != sk_D_2 )
      | ( ( k2_tarski @ sk_D_2 @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_2 @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,
    ( ( ( k2_tarski @ sk_D_2 @ sk_D_2 )
      = k1_xboole_0 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('30',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('31',plain,
    ( ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
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

thf('33',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k2_mcart_1 @ X33 ) )
      | ( X33
       != ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('34',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != ( k2_mcart_1 @ ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X44: $i,X46: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X44 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('36',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != X35 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('40',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('41',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('42',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('43',plain,
    ( ( sk_D_2
      = ( k3_mcart_1 @ sk_D_2 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k2_mcart_1 @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_2 )
        | ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_2 ) )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( sk_D_2 != sk_D_2 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_2 ) )
          = X0 )
        | ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 )
        | ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_2 ) )
          = X0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_D_2
      = ( k3_mcart_1 @ sk_D_2 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k2_mcart_1 @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('50',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('51',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X44 @ X45 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_mcart_1 @ sk_D_2 )
      = ( k4_tarski @ sk_D_2 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( k1_mcart_1 @ sk_D_2 )
      = ( k4_tarski @ sk_D_2 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('55',plain,(
    ! [X44: $i,X46: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X44 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('56',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) )
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_mcart_1 @ sk_D_2 )
      = ( k4_tarski @ sk_D_2 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ sk_D_2 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_D_2 ) @ X0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('61',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_B @ X1 )
         != ( k4_tarski @ ( k1_mcart_1 @ sk_D_2 ) @ X0 ) )
        | ~ ( r2_hidden @ sk_D_2 @ X1 )
        | ( X1 = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0
         != ( k4_tarski @ ( k1_mcart_1 @ sk_D_2 ) @ X1 ) )
        | ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 )
        | ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 )
        | ~ ( r2_hidden @ sk_D_2 @ ( k2_tarski @ X0 @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0
         != ( k4_tarski @ ( k1_mcart_1 @ sk_D_2 ) @ X1 ) )
        | ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 )
        | ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X1: $i] :
        ( ( k2_tarski @ ( k4_tarski @ ( k1_mcart_1 @ sk_D_2 ) @ X1 ) @ sk_D_2 )
        = k1_xboole_0 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X3 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('67',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_D_2 ) @ X0 ) @ k1_xboole_0 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_2 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_D_2 ) )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('71',plain,
    ( ( ( sk_D_2 != sk_D_2 )
      | ( ( k2_tarski @ sk_D_2 @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D_2 @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_tarski @ sk_D_2 @ sk_D_2 )
      = k1_xboole_0 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_D_2 )
        | ( X0 = sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_D_2 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( k4_tarski @ ( k1_mcart_1 @ sk_D_2 ) @ X0 )
        = sk_D_2 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != X35 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('78',plain,
    ( ! [X0: $i] : ( sk_D_2 != X0 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_D_2
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('81',plain,
    ( sk_D_2
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['38','79','80'])).

thf('82',plain,
    ( ( k2_tarski @ sk_D_2 @ sk_D_2 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','81'])).

thf('83',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('84',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('85',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X13 )
      | ~ ( r2_hidden @ X8 @ X13 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ( X10
       != ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,(
    ! [X8: $i,X9: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X8 @ X13 )
      | ( zip_tseitin_0 @ X9 @ X8 @ ( k4_tarski @ X8 @ X9 ) @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X0 @ X3 @ ( k4_tarski @ X3 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( zip_tseitin_0 @ X2 @ X0 @ ( k4_tarski @ X0 @ X2 ) @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','87'])).

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

thf('89',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X16 @ X19 )
      | ( X19
       != ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','91'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('93',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('94',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','94'])).

thf('96',plain,
    ( ( ( k2_tarski @ sk_D_2 @ sk_D_2 )
      = k1_xboole_0 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('97',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_D_2 )
        | ( X0 = sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_D_2 )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( sk_D_2
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['38','79','80'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D_2 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_tarski @ sk_D_2 @ X0 )
      = sk_D_2 ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_mcart_1 @ X33 ) )
      | ( X33
       != ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('104',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != ( k1_mcart_1 @ ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X44 @ X45 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('106',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != X34 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3tzu6GzLKT
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.84/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.05  % Solved by: fo/fo7.sh
% 0.84/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.05  % done 593 iterations in 0.578s
% 0.84/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.05  % SZS output start Refutation
% 0.84/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.05  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.05  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.84/1.05  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.84/1.05  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.84/1.05  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.05  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.84/1.05  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.84/1.05  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.05  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.84/1.05  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.84/1.05  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.84/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.05  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.84/1.05  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.84/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.05  thf(t29_mcart_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.84/1.05          ( ![B:$i]:
% 0.84/1.05            ( ~( ( r2_hidden @ B @ A ) & 
% 0.84/1.05                 ( ![C:$i,D:$i,E:$i]:
% 0.84/1.05                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.84/1.05                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf('0', plain,
% 0.84/1.05      (![X36 : $i]:
% 0.84/1.05         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X36) @ X36))),
% 0.84/1.05      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.84/1.05  thf(d2_tarski, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.84/1.05       ( ![D:$i]:
% 0.84/1.05         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.84/1.05  thf('1', plain,
% 0.84/1.05      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X4 @ X2)
% 0.84/1.05          | ((X4) = (X3))
% 0.84/1.05          | ((X4) = (X0))
% 0.84/1.05          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.84/1.05      inference('cnf', [status(esa)], [d2_tarski])).
% 0.84/1.05  thf('2', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.84/1.05         (((X4) = (X0))
% 0.84/1.05          | ((X4) = (X3))
% 0.84/1.05          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['1'])).
% 0.84/1.05  thf('3', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.84/1.05          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.84/1.05          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['0', '2'])).
% 0.84/1.05  thf('4', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (((X0) != (X1))
% 0.84/1.05          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.84/1.05          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 0.84/1.05      inference('eq_fact', [status(thm)], ['3'])).
% 0.84/1.05  thf('5', plain,
% 0.84/1.05      (![X1 : $i]:
% 0.84/1.05         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.84/1.05          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['4'])).
% 0.84/1.05  thf('6', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         (((X1) != (X0))
% 0.84/1.05          | (r2_hidden @ X1 @ X2)
% 0.84/1.05          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.84/1.05      inference('cnf', [status(esa)], [d2_tarski])).
% 0.84/1.05  thf('7', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.84/1.05      inference('simplify', [status(thm)], ['6'])).
% 0.84/1.05  thf(t51_mcart_1, conjecture,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.84/1.05          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.84/1.05          ( ~( ![D:$i]:
% 0.84/1.05               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.84/1.05                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.84/1.05                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.84/1.05                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.05    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.05        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.84/1.05             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.84/1.05             ( ~( ![D:$i]:
% 0.84/1.05                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.84/1.05                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.84/1.05                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.84/1.05                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.84/1.05    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.84/1.05  thf('8', plain,
% 0.84/1.05      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 0.84/1.05        | ((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 0.84/1.05        | ((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('9', plain,
% 0.84/1.05      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.84/1.05         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('split', [status(esa)], ['8'])).
% 0.84/1.05  thf('10', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(t48_mcart_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.84/1.05          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.84/1.05          ( ~( ![D:$i]:
% 0.84/1.05               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.84/1.05                 ( ( D ) =
% 0.84/1.05                   ( k3_mcart_1 @
% 0.84/1.05                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.84/1.05                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.84/1.05                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf('11', plain,
% 0.84/1.05      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.84/1.05         (((X40) = (k1_xboole_0))
% 0.84/1.05          | ((X41) = (k1_xboole_0))
% 0.84/1.05          | ((X43)
% 0.84/1.05              = (k3_mcart_1 @ (k5_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.84/1.05                 (k6_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.84/1.05                 (k7_mcart_1 @ X40 @ X41 @ X42 @ X43)))
% 0.84/1.05          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X40 @ X41 @ X42))
% 0.84/1.05          | ((X42) = (k1_xboole_0)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.84/1.05  thf('12', plain,
% 0.84/1.05      ((((sk_C) = (k1_xboole_0))
% 0.84/1.05        | ((sk_D_2)
% 0.84/1.05            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.84/1.05        | ((sk_B_1) = (k1_xboole_0))
% 0.84/1.05        | ((sk_A) = (k1_xboole_0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.05  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('16', plain,
% 0.84/1.05      (((sk_D_2)
% 0.84/1.05         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.84/1.05  thf('17', plain,
% 0.84/1.05      (((sk_D_2)
% 0.84/1.05         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.84/1.05  thf(d3_mcart_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.84/1.05  thf('18', plain,
% 0.84/1.05      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.05         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.84/1.05           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.84/1.05  thf(t7_mcart_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.84/1.05       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.84/1.05  thf('19', plain,
% 0.84/1.05      (![X44 : $i, X46 : $i]: ((k2_mcart_1 @ (k4_tarski @ X44 @ X46)) = (X46))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.84/1.05  thf('20', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['18', '19'])).
% 0.84/1.05  thf('21', plain,
% 0.84/1.05      (((k2_mcart_1 @ sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))),
% 0.84/1.05      inference('sup+', [status(thm)], ['17', '20'])).
% 0.84/1.05  thf('22', plain,
% 0.84/1.05      (((sk_D_2)
% 0.84/1.05         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k2_mcart_1 @ sk_D_2)))),
% 0.84/1.05      inference('demod', [status(thm)], ['16', '21'])).
% 0.84/1.05  thf('23', plain,
% 0.84/1.05      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.84/1.05         (((X36) = (k1_xboole_0))
% 0.84/1.05          | ~ (r2_hidden @ X37 @ X36)
% 0.84/1.05          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.84/1.05  thf('24', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (((sk_B @ X0) != (sk_D_2))
% 0.84/1.05          | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ X0)
% 0.84/1.05          | ((X0) = (k1_xboole_0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['22', '23'])).
% 0.84/1.05  thf('25', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (~ (r2_hidden @ sk_D_2 @ X0)
% 0.84/1.05           | ((X0) = (k1_xboole_0))
% 0.84/1.05           | ((sk_B @ X0) != (sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['9', '24'])).
% 0.84/1.05  thf('26', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (((sk_B @ (k2_tarski @ X0 @ sk_D_2)) != (sk_D_2))
% 0.84/1.05           | ((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))))
% 0.84/1.05         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['7', '25'])).
% 0.84/1.05  thf('27', plain,
% 0.84/1.05      (((((sk_D_2) != (sk_D_2))
% 0.84/1.05         | ((k2_tarski @ sk_D_2 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05         | ((k2_tarski @ sk_D_2 @ sk_D_2) = (k1_xboole_0))))
% 0.84/1.05         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['5', '26'])).
% 0.84/1.05  thf('28', plain,
% 0.84/1.05      ((((k2_tarski @ sk_D_2 @ sk_D_2) = (k1_xboole_0)))
% 0.84/1.05         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['27'])).
% 0.84/1.05  thf('29', plain,
% 0.84/1.05      ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.84/1.05         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('split', [status(esa)], ['8'])).
% 0.84/1.05  thf('30', plain,
% 0.84/1.05      (((sk_D_2)
% 0.84/1.05         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.84/1.05  thf('31', plain,
% 0.84/1.05      ((((sk_D_2)
% 0.84/1.05          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ sk_D_2)))
% 0.84/1.05         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['29', '30'])).
% 0.84/1.05  thf('32', plain,
% 0.84/1.05      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.05         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.84/1.05           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.84/1.05  thf(t20_mcart_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.84/1.05       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.84/1.05  thf('33', plain,
% 0.84/1.05      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.84/1.05         (((X33) != (k2_mcart_1 @ X33)) | ((X33) != (k4_tarski @ X34 @ X35)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.84/1.05  thf('34', plain,
% 0.84/1.05      (![X34 : $i, X35 : $i]:
% 0.84/1.05         ((k4_tarski @ X34 @ X35) != (k2_mcart_1 @ (k4_tarski @ X34 @ X35)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['33'])).
% 0.84/1.05  thf('35', plain,
% 0.84/1.05      (![X44 : $i, X46 : $i]: ((k2_mcart_1 @ (k4_tarski @ X44 @ X46)) = (X46))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.84/1.05  thf('36', plain, (![X34 : $i, X35 : $i]: ((k4_tarski @ X34 @ X35) != (X35))),
% 0.84/1.05      inference('demod', [status(thm)], ['34', '35'])).
% 0.84/1.05  thf('37', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['32', '36'])).
% 0.84/1.05  thf('38', plain,
% 0.84/1.05      (~ (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['31', '37'])).
% 0.84/1.05  thf('39', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.84/1.05          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.84/1.05          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['0', '2'])).
% 0.84/1.05  thf('40', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.84/1.05      inference('simplify', [status(thm)], ['6'])).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('split', [status(esa)], ['8'])).
% 0.84/1.05  thf('42', plain,
% 0.84/1.05      (((sk_D_2)
% 0.84/1.05         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05            (k2_mcart_1 @ sk_D_2)))),
% 0.84/1.05      inference('demod', [status(thm)], ['16', '21'])).
% 0.84/1.05  thf('43', plain,
% 0.84/1.05      ((((sk_D_2)
% 0.84/1.05          = (k3_mcart_1 @ sk_D_2 @ 
% 0.84/1.05             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05             (k2_mcart_1 @ sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['41', '42'])).
% 0.84/1.05  thf('44', plain,
% 0.84/1.05      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.84/1.05         (((X36) = (k1_xboole_0))
% 0.84/1.05          | ~ (r2_hidden @ X38 @ X36)
% 0.84/1.05          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.84/1.05  thf('45', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (((sk_B @ X0) != (sk_D_2))
% 0.84/1.05           | ~ (r2_hidden @ sk_D_2 @ X0)
% 0.84/1.05           | ((X0) = (k1_xboole_0))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['43', '44'])).
% 0.84/1.05  thf('46', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05           | ((sk_B @ (k2_tarski @ X0 @ sk_D_2)) != (sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['40', '45'])).
% 0.84/1.05  thf('47', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (((sk_D_2) != (sk_D_2))
% 0.84/1.05           | ((sk_B @ (k2_tarski @ X0 @ sk_D_2)) = (X0))
% 0.84/1.05           | ((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05           | ((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['39', '46'])).
% 0.84/1.05  thf('48', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05           | ((sk_B @ (k2_tarski @ X0 @ sk_D_2)) = (X0))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['47'])).
% 0.84/1.05  thf('49', plain,
% 0.84/1.05      ((((sk_D_2)
% 0.84/1.05          = (k3_mcart_1 @ sk_D_2 @ 
% 0.84/1.05             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 0.84/1.05             (k2_mcart_1 @ sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['41', '42'])).
% 0.84/1.05  thf('50', plain,
% 0.84/1.05      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.05         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.84/1.05           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.84/1.05  thf('51', plain,
% 0.84/1.05      (![X44 : $i, X45 : $i]: ((k1_mcart_1 @ (k4_tarski @ X44 @ X45)) = (X44))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.84/1.05  thf('52', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['50', '51'])).
% 0.84/1.05  thf('53', plain,
% 0.84/1.05      ((((k1_mcart_1 @ sk_D_2)
% 0.84/1.05          = (k4_tarski @ sk_D_2 @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['49', '52'])).
% 0.84/1.05  thf('54', plain,
% 0.84/1.05      ((((k1_mcart_1 @ sk_D_2)
% 0.84/1.05          = (k4_tarski @ sk_D_2 @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['49', '52'])).
% 0.84/1.05  thf('55', plain,
% 0.84/1.05      (![X44 : $i, X46 : $i]: ((k2_mcart_1 @ (k4_tarski @ X44 @ X46)) = (X46))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.84/1.05  thf('56', plain,
% 0.84/1.05      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_D_2))
% 0.84/1.05          = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['54', '55'])).
% 0.84/1.05  thf('57', plain,
% 0.84/1.05      ((((k1_mcart_1 @ sk_D_2)
% 0.84/1.05          = (k4_tarski @ sk_D_2 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('demod', [status(thm)], ['53', '56'])).
% 0.84/1.05  thf('58', plain,
% 0.84/1.05      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.05         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.84/1.05           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.84/1.05  thf('59', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          ((k3_mcart_1 @ sk_D_2 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ X0)
% 0.84/1.05            = (k4_tarski @ (k1_mcart_1 @ sk_D_2) @ X0)))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['57', '58'])).
% 0.84/1.05  thf('60', plain,
% 0.84/1.05      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.84/1.05         (((X36) = (k1_xboole_0))
% 0.84/1.05          | ~ (r2_hidden @ X38 @ X36)
% 0.84/1.05          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.84/1.05  thf('61', plain,
% 0.84/1.05      ((![X0 : $i, X1 : $i]:
% 0.84/1.05          (((sk_B @ X1) != (k4_tarski @ (k1_mcart_1 @ sk_D_2) @ X0))
% 0.84/1.05           | ~ (r2_hidden @ sk_D_2 @ X1)
% 0.84/1.05           | ((X1) = (k1_xboole_0))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['59', '60'])).
% 0.84/1.05  thf('62', plain,
% 0.84/1.05      ((![X0 : $i, X1 : $i]:
% 0.84/1.05          (((X0) != (k4_tarski @ (k1_mcart_1 @ sk_D_2) @ X1))
% 0.84/1.05           | ((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05           | ((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05           | ~ (r2_hidden @ sk_D_2 @ (k2_tarski @ X0 @ sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['48', '61'])).
% 0.84/1.05  thf('63', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.84/1.05      inference('simplify', [status(thm)], ['6'])).
% 0.84/1.05  thf('64', plain,
% 0.84/1.05      ((![X0 : $i, X1 : $i]:
% 0.84/1.05          (((X0) != (k4_tarski @ (k1_mcart_1 @ sk_D_2) @ X1))
% 0.84/1.05           | ((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05           | ((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('demod', [status(thm)], ['62', '63'])).
% 0.84/1.05  thf('65', plain,
% 0.84/1.05      ((![X1 : $i]:
% 0.84/1.05          ((k2_tarski @ (k4_tarski @ (k1_mcart_1 @ sk_D_2) @ X1) @ sk_D_2)
% 0.84/1.05            = (k1_xboole_0)))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['64'])).
% 0.84/1.05  thf('66', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         (((X1) != (X3))
% 0.84/1.05          | (r2_hidden @ X1 @ X2)
% 0.84/1.05          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.84/1.05      inference('cnf', [status(esa)], [d2_tarski])).
% 0.84/1.05  thf('67', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 0.84/1.05      inference('simplify', [status(thm)], ['66'])).
% 0.84/1.05  thf('68', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_D_2) @ X0) @ k1_xboole_0))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['65', '67'])).
% 0.84/1.05  thf('69', plain,
% 0.84/1.05      (![X1 : $i]:
% 0.84/1.05         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.84/1.05          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['4'])).
% 0.84/1.05  thf('70', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (((k2_tarski @ X0 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05           | ((sk_B @ (k2_tarski @ X0 @ sk_D_2)) != (sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['40', '45'])).
% 0.84/1.05  thf('71', plain,
% 0.84/1.05      (((((sk_D_2) != (sk_D_2))
% 0.84/1.05         | ((k2_tarski @ sk_D_2 @ sk_D_2) = (k1_xboole_0))
% 0.84/1.05         | ((k2_tarski @ sk_D_2 @ sk_D_2) = (k1_xboole_0))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['69', '70'])).
% 0.84/1.05  thf('72', plain,
% 0.84/1.05      ((((k2_tarski @ sk_D_2 @ sk_D_2) = (k1_xboole_0)))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['71'])).
% 0.84/1.05  thf('73', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.84/1.05         (((X4) = (X0))
% 0.84/1.05          | ((X4) = (X3))
% 0.84/1.05          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['1'])).
% 0.84/1.05  thf('74', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.84/1.05           | ((X0) = (sk_D_2))
% 0.84/1.05           | ((X0) = (sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['72', '73'])).
% 0.84/1.05  thf('75', plain,
% 0.84/1.05      ((![X0 : $i]: (((X0) = (sk_D_2)) | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['74'])).
% 0.84/1.05  thf('76', plain,
% 0.84/1.05      ((![X0 : $i]: ((k4_tarski @ (k1_mcart_1 @ sk_D_2) @ X0) = (sk_D_2)))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['68', '75'])).
% 0.84/1.05  thf('77', plain, (![X34 : $i, X35 : $i]: ((k4_tarski @ X34 @ X35) != (X35))),
% 0.84/1.05      inference('demod', [status(thm)], ['34', '35'])).
% 0.84/1.05  thf('78', plain,
% 0.84/1.05      ((![X0 : $i]: ((sk_D_2) != (X0)))
% 0.84/1.05         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['76', '77'])).
% 0.84/1.05  thf('79', plain,
% 0.84/1.05      (~ (((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['78'])).
% 0.84/1.05  thf('80', plain,
% 0.84/1.05      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))) | 
% 0.84/1.05       (((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))) | 
% 0.84/1.05       (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('split', [status(esa)], ['8'])).
% 0.84/1.05  thf('81', plain,
% 0.84/1.05      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('sat_resolution*', [status(thm)], ['38', '79', '80'])).
% 0.84/1.05  thf('82', plain, (((k2_tarski @ sk_D_2 @ sk_D_2) = (k1_xboole_0))),
% 0.84/1.05      inference('simpl_trail', [status(thm)], ['28', '81'])).
% 0.84/1.05  thf('83', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.84/1.05      inference('simplify', [status(thm)], ['6'])).
% 0.84/1.05  thf('84', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.84/1.05      inference('simplify', [status(thm)], ['6'])).
% 0.84/1.05  thf(d2_zfmisc_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.84/1.05       ( ![D:$i]:
% 0.84/1.05         ( ( r2_hidden @ D @ C ) <=>
% 0.84/1.05           ( ?[E:$i,F:$i]:
% 0.84/1.05             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.84/1.05               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.84/1.05  thf(zf_stmt_1, axiom,
% 0.84/1.05    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.84/1.05     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.84/1.05       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.84/1.05         ( r2_hidden @ E @ A ) ) ))).
% 0.84/1.05  thf('85', plain,
% 0.84/1.05      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.84/1.05         ((zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X13)
% 0.84/1.05          | ~ (r2_hidden @ X8 @ X13)
% 0.84/1.05          | ~ (r2_hidden @ X9 @ X11)
% 0.84/1.05          | ((X10) != (k4_tarski @ X8 @ X9)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.05  thf('86', plain,
% 0.84/1.05      (![X8 : $i, X9 : $i, X11 : $i, X13 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X9 @ X11)
% 0.84/1.05          | ~ (r2_hidden @ X8 @ X13)
% 0.84/1.05          | (zip_tseitin_0 @ X9 @ X8 @ (k4_tarski @ X8 @ X9) @ X11 @ X13))),
% 0.84/1.05      inference('simplify', [status(thm)], ['85'])).
% 0.84/1.05  thf('87', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         ((zip_tseitin_0 @ X0 @ X3 @ (k4_tarski @ X3 @ X0) @ 
% 0.84/1.05           (k2_tarski @ X1 @ X0) @ X2)
% 0.84/1.05          | ~ (r2_hidden @ X3 @ X2))),
% 0.84/1.05      inference('sup-', [status(thm)], ['84', '86'])).
% 0.84/1.05  thf('88', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         (zip_tseitin_0 @ X2 @ X0 @ (k4_tarski @ X0 @ X2) @ 
% 0.84/1.05          (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['83', '87'])).
% 0.84/1.05  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.84/1.05  thf(zf_stmt_3, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.84/1.05       ( ![D:$i]:
% 0.84/1.05         ( ( r2_hidden @ D @ C ) <=>
% 0.84/1.05           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.84/1.05  thf('89', plain,
% 0.84/1.05      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.84/1.05         (~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.84/1.05          | (r2_hidden @ X16 @ X19)
% 0.84/1.05          | ((X19) != (k2_zfmisc_1 @ X18 @ X17)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.84/1.05  thf('90', plain,
% 0.84/1.05      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.84/1.05         ((r2_hidden @ X16 @ (k2_zfmisc_1 @ X18 @ X17))
% 0.84/1.05          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.84/1.05      inference('simplify', [status(thm)], ['89'])).
% 0.84/1.05  thf('91', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 0.84/1.05          (k2_zfmisc_1 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['88', '90'])).
% 0.84/1.05  thf('92', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (r2_hidden @ (k4_tarski @ sk_D_2 @ X0) @ 
% 0.84/1.05          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['82', '91'])).
% 0.84/1.05  thf(t113_zfmisc_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.84/1.05       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.84/1.05  thf('93', plain,
% 0.84/1.05      (![X25 : $i, X26 : $i]:
% 0.84/1.05         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.84/1.05          | ((X25) != (k1_xboole_0)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.84/1.05  thf('94', plain,
% 0.84/1.05      (![X26 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 0.84/1.05      inference('simplify', [status(thm)], ['93'])).
% 0.84/1.05  thf('95', plain,
% 0.84/1.05      (![X0 : $i]: (r2_hidden @ (k4_tarski @ sk_D_2 @ X0) @ k1_xboole_0)),
% 0.84/1.05      inference('demod', [status(thm)], ['92', '94'])).
% 0.84/1.05  thf('96', plain,
% 0.84/1.05      ((((k2_tarski @ sk_D_2 @ sk_D_2) = (k1_xboole_0)))
% 0.84/1.05         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['27'])).
% 0.84/1.05  thf('97', plain,
% 0.84/1.05      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.84/1.05         (((X4) = (X0))
% 0.84/1.05          | ((X4) = (X3))
% 0.84/1.05          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['1'])).
% 0.84/1.05  thf('98', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.84/1.05           | ((X0) = (sk_D_2))
% 0.84/1.05           | ((X0) = (sk_D_2))))
% 0.84/1.05         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['96', '97'])).
% 0.84/1.05  thf('99', plain,
% 0.84/1.05      ((![X0 : $i]: (((X0) = (sk_D_2)) | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 0.84/1.05         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['98'])).
% 0.84/1.05  thf('100', plain,
% 0.84/1.05      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 0.84/1.05      inference('sat_resolution*', [status(thm)], ['38', '79', '80'])).
% 0.84/1.05  thf('101', plain,
% 0.84/1.05      (![X0 : $i]: (((X0) = (sk_D_2)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.84/1.05      inference('simpl_trail', [status(thm)], ['99', '100'])).
% 0.84/1.05  thf('102', plain, (![X0 : $i]: ((k4_tarski @ sk_D_2 @ X0) = (sk_D_2))),
% 0.84/1.05      inference('sup-', [status(thm)], ['95', '101'])).
% 0.84/1.05  thf('103', plain,
% 0.84/1.05      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.84/1.05         (((X33) != (k1_mcart_1 @ X33)) | ((X33) != (k4_tarski @ X34 @ X35)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.84/1.05  thf('104', plain,
% 0.84/1.05      (![X34 : $i, X35 : $i]:
% 0.84/1.05         ((k4_tarski @ X34 @ X35) != (k1_mcart_1 @ (k4_tarski @ X34 @ X35)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['103'])).
% 0.84/1.05  thf('105', plain,
% 0.84/1.05      (![X44 : $i, X45 : $i]: ((k1_mcart_1 @ (k4_tarski @ X44 @ X45)) = (X44))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.84/1.05  thf('106', plain,
% 0.84/1.05      (![X34 : $i, X35 : $i]: ((k4_tarski @ X34 @ X35) != (X34))),
% 0.84/1.05      inference('demod', [status(thm)], ['104', '105'])).
% 0.84/1.05  thf('107', plain, ($false),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['102', '106'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
