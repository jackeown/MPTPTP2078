%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g57UrUytIR

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 508 expanded)
%              Number of leaves         :   35 ( 169 expanded)
%              Depth                    :   15
%              Number of atoms          : 1312 (8714 expanded)
%              Number of equality atoms :  203 (1370 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( X8 = X7 )
      | ( X8 = X4 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ( X8 = X4 )
      | ( X8 = X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X14 @ ( k1_tarski @ X13 ) )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

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

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k3_zfmisc_1 @ X37 @ X38 @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( sk_D_1
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('36',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X36
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X33 @ X34 @ X35 @ X36 ) @ ( k6_mcart_1 @ X33 @ X34 @ X35 @ X36 ) @ ( k7_mcart_1 @ X33 @ X34 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k3_zfmisc_1 @ X33 @ X34 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('37',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('38',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X36
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X33 @ X34 @ X35 @ X36 ) @ ( k6_mcart_1 @ X33 @ X34 @ X35 @ X36 ) @ ( k7_mcart_1 @ X33 @ X34 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('42',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k3_zfmisc_1 @ X37 @ X38 @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('44',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k2_mcart_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k3_zfmisc_1 @ X37 @ X38 @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k2_mcart_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ sk_D_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','49','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ( ( sk_B @ X29 )
       != ( k3_mcart_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['34','65'])).

thf('67',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('69',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
     != sk_D_1 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','69'])).

thf('71',plain,
    ( $false
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['54','55','56','57'])).

thf('73',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['32'])).

thf('74',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('76',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('77',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_mcart_1 @ X20 @ X21 @ X22 )
      = ( k4_tarski @ ( k4_tarski @ X20 @ X21 ) @ X22 ) ) ),
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

thf('78',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k2_mcart_1 @ X26 ) )
      | ( X26
       != ( k4_tarski @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_tarski @ X27 @ X28 )
     != ( k2_mcart_1 @ ( k4_tarski @ X27 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('80',plain,(
    ! [X41: $i,X43: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X41 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('81',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_tarski @ X27 @ X28 )
     != X28 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['76','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['6','18'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('86',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46','47','48'])).

thf('87',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['32'])).

thf('88',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('90',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r2_hidden @ X30 @ X29 )
      | ( ( sk_B @ X29 )
       != ( k3_mcart_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('95',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
     != sk_D_1 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['84','95'])).

thf('97',plain,(
    sk_D_1
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['32'])).

thf('99',plain,
    ( sk_D_1
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['83','97','98'])).

thf('100',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['71','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g57UrUytIR
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:04:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 313 iterations in 0.103s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.54  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.54  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.19/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.55  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(t29_mcart_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55          ( ![B:$i]:
% 0.19/0.55            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.55                 ( ![C:$i,D:$i,E:$i]:
% 0.19/0.55                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.19/0.55                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      (![X29 : $i]:
% 0.19/0.55         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X29) @ X29))),
% 0.19/0.55      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.19/0.55  thf(t69_enumset1, axiom,
% 0.19/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.55  thf('1', plain, (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.19/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.55  thf(d2_tarski, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.55       ( ![D:$i]:
% 0.19/0.55         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X8 @ X6)
% 0.19/0.55          | ((X8) = (X7))
% 0.19/0.55          | ((X8) = (X4))
% 0.19/0.55          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (![X4 : $i, X7 : $i, X8 : $i]:
% 0.19/0.55         (((X8) = (X4))
% 0.19/0.55          | ((X8) = (X7))
% 0.19/0.55          | ~ (r2_hidden @ X8 @ (k2_tarski @ X7 @ X4)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.19/0.55          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['0', '5'])).
% 0.19/0.55  thf(t3_boole, axiom,
% 0.19/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.55  thf('7', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.55  thf(t48_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      (![X2 : $i, X3 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.19/0.55           = (k3_xboole_0 @ X2 @ X3))),
% 0.19/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.55  thf(t2_boole, axiom,
% 0.19/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.55  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.55  thf(t65_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.19/0.55       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      (![X13 : $i, X14 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X13 @ X14)
% 0.19/0.55          | ((k4_xboole_0 @ X14 @ (k1_tarski @ X13)) != (X14)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.19/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.19/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.55         (((X5) != (X4))
% 0.19/0.55          | (r2_hidden @ X5 @ X6)
% 0.19/0.55          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.19/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.55  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['14', '16'])).
% 0.19/0.55  thf('18', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.19/0.55      inference('demod', [status(thm)], ['13', '17'])).
% 0.19/0.55  thf('19', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.19/0.55      inference('clc', [status(thm)], ['6', '18'])).
% 0.19/0.55  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['14', '16'])).
% 0.19/0.55  thf(t51_mcart_1, conjecture,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55          ( ~( ![D:$i]:
% 0.19/0.55               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.55                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.55                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.55                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.55        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55             ( ~( ![D:$i]:
% 0.19/0.55                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.55                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.55                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.55                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d3_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.19/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.55         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.19/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.55        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.19/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.55  thf(t50_mcart_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55          ( ~( ![D:$i]:
% 0.19/0.55               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.55                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.55                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.55                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.55                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.19/0.55         (((X37) = (k1_xboole_0))
% 0.19/0.55          | ((X38) = (k1_xboole_0))
% 0.19/0.55          | ((k5_mcart_1 @ X37 @ X38 @ X40 @ X39)
% 0.19/0.55              = (k1_mcart_1 @ (k1_mcart_1 @ X39)))
% 0.19/0.55          | ~ (m1_subset_1 @ X39 @ (k3_zfmisc_1 @ X37 @ X38 @ X40))
% 0.19/0.55          | ((X40) = (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.55         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.19/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.19/0.55         (((X37) = (k1_xboole_0))
% 0.19/0.55          | ((X38) = (k1_xboole_0))
% 0.19/0.55          | ((k5_mcart_1 @ X37 @ X38 @ X40 @ X39)
% 0.19/0.55              = (k1_mcart_1 @ (k1_mcart_1 @ X39)))
% 0.19/0.55          | ~ (m1_subset_1 @ X39 @ 
% 0.19/0.55               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X40))
% 0.19/0.55          | ((X40) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      ((((sk_C) = (k1_xboole_0))
% 0.19/0.55        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.19/0.55            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.19/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['23', '26'])).
% 0.19/0.55  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('29', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.19/0.55         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.19/0.55        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.19/0.55        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('split', [status(esa)], ['32'])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      ((((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.19/0.55         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['31', '33'])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.55        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.19/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.55  thf(t48_mcart_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55          ( ~( ![D:$i]:
% 0.19/0.55               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.55                 ( ( D ) =
% 0.19/0.55                   ( k3_mcart_1 @
% 0.19/0.55                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.55                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.55                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.19/0.55         (((X33) = (k1_xboole_0))
% 0.19/0.55          | ((X34) = (k1_xboole_0))
% 0.19/0.55          | ((X36)
% 0.19/0.55              = (k3_mcart_1 @ (k5_mcart_1 @ X33 @ X34 @ X35 @ X36) @ 
% 0.19/0.55                 (k6_mcart_1 @ X33 @ X34 @ X35 @ X36) @ 
% 0.19/0.55                 (k7_mcart_1 @ X33 @ X34 @ X35 @ X36)))
% 0.19/0.55          | ~ (m1_subset_1 @ X36 @ (k3_zfmisc_1 @ X33 @ X34 @ X35))
% 0.19/0.55          | ((X35) = (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.55         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.19/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.19/0.55         (((X33) = (k1_xboole_0))
% 0.19/0.55          | ((X34) = (k1_xboole_0))
% 0.19/0.55          | ((X36)
% 0.19/0.55              = (k3_mcart_1 @ (k5_mcart_1 @ X33 @ X34 @ X35 @ X36) @ 
% 0.19/0.55                 (k6_mcart_1 @ X33 @ X34 @ X35 @ X36) @ 
% 0.19/0.55                 (k7_mcart_1 @ X33 @ X34 @ X35 @ X36)))
% 0.19/0.55          | ~ (m1_subset_1 @ X36 @ 
% 0.19/0.55               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34) @ X35))
% 0.19/0.55          | ((X35) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      ((((sk_C) = (k1_xboole_0))
% 0.19/0.55        | ((sk_D_1)
% 0.19/0.55            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.19/0.55               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.19/0.55               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.19/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['35', '38'])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.19/0.55         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.55        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.19/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.19/0.55         (((X37) = (k1_xboole_0))
% 0.19/0.55          | ((X38) = (k1_xboole_0))
% 0.19/0.55          | ((k6_mcart_1 @ X37 @ X38 @ X40 @ X39)
% 0.19/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X39)))
% 0.19/0.55          | ~ (m1_subset_1 @ X39 @ (k3_zfmisc_1 @ X37 @ X38 @ X40))
% 0.19/0.55          | ((X40) = (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.55  thf('43', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.55         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.19/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.55  thf('44', plain,
% 0.19/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.19/0.55         (((X37) = (k1_xboole_0))
% 0.19/0.55          | ((X38) = (k1_xboole_0))
% 0.19/0.55          | ((k6_mcart_1 @ X37 @ X38 @ X40 @ X39)
% 0.19/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X39)))
% 0.19/0.55          | ~ (m1_subset_1 @ X39 @ 
% 0.19/0.55               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X40))
% 0.19/0.55          | ((X40) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.55  thf('45', plain,
% 0.19/0.55      ((((sk_C) = (k1_xboole_0))
% 0.19/0.55        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.19/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.19/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['41', '44'])).
% 0.19/0.55  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('47', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('48', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('49', plain,
% 0.19/0.55      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.19/0.55         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['45', '46', '47', '48'])).
% 0.19/0.55  thf('50', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.55        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.19/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.55  thf('51', plain,
% 0.19/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.19/0.55         (((X37) = (k1_xboole_0))
% 0.19/0.55          | ((X38) = (k1_xboole_0))
% 0.19/0.55          | ((k7_mcart_1 @ X37 @ X38 @ X40 @ X39) = (k2_mcart_1 @ X39))
% 0.19/0.55          | ~ (m1_subset_1 @ X39 @ (k3_zfmisc_1 @ X37 @ X38 @ X40))
% 0.19/0.55          | ((X40) = (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.55  thf('52', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.55         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.19/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.19/0.55         (((X37) = (k1_xboole_0))
% 0.19/0.55          | ((X38) = (k1_xboole_0))
% 0.19/0.55          | ((k7_mcart_1 @ X37 @ X38 @ X40 @ X39) = (k2_mcart_1 @ X39))
% 0.19/0.55          | ~ (m1_subset_1 @ X39 @ 
% 0.19/0.55               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38) @ X40))
% 0.19/0.55          | ((X40) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.55  thf('54', plain,
% 0.19/0.55      ((((sk_C) = (k1_xboole_0))
% 0.19/0.55        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))
% 0.19/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['50', '53'])).
% 0.19/0.55  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('56', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('57', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['54', '55', '56', '57'])).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      ((((sk_C) = (k1_xboole_0))
% 0.19/0.55        | ((sk_D_1)
% 0.19/0.55            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.19/0.55               (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))
% 0.19/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['39', '40', '49', '58'])).
% 0.19/0.55  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('61', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('63', plain,
% 0.19/0.55      (((sk_D_1)
% 0.19/0.55         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.19/0.55            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.19/0.55  thf('64', plain,
% 0.19/0.55      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.55         (((X29) = (k1_xboole_0))
% 0.19/0.55          | ~ (r2_hidden @ X31 @ X29)
% 0.19/0.55          | ((sk_B @ X29) != (k3_mcart_1 @ X31 @ X30 @ X32)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.19/0.55  thf('65', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (((sk_B @ X0) != (sk_D_1))
% 0.19/0.55          | ~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ X0)
% 0.19/0.55          | ((X0) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.19/0.55  thf('66', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          (~ (r2_hidden @ sk_D_1 @ X0)
% 0.19/0.55           | ((X0) = (k1_xboole_0))
% 0.19/0.55           | ((sk_B @ X0) != (sk_D_1))))
% 0.19/0.55         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['34', '65'])).
% 0.19/0.55  thf('67', plain,
% 0.19/0.55      (((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.19/0.55         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.19/0.55         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['20', '66'])).
% 0.19/0.55  thf('68', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.19/0.55      inference('demod', [status(thm)], ['13', '17'])).
% 0.19/0.55  thf('69', plain,
% 0.19/0.55      ((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('clc', [status(thm)], ['67', '68'])).
% 0.19/0.55  thf('70', plain,
% 0.19/0.55      ((((sk_D_1) != (sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['19', '69'])).
% 0.19/0.55  thf('71', plain,
% 0.19/0.55      (($false)
% 0.19/0.55         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('simplify', [status(thm)], ['70'])).
% 0.19/0.55  thf('72', plain,
% 0.19/0.55      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['54', '55', '56', '57'])).
% 0.19/0.55  thf('73', plain,
% 0.19/0.55      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('split', [status(esa)], ['32'])).
% 0.19/0.55  thf('74', plain,
% 0.19/0.55      ((((sk_D_1) = (k2_mcart_1 @ sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['72', '73'])).
% 0.19/0.55  thf('75', plain,
% 0.19/0.55      (((sk_D_1)
% 0.19/0.55         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.19/0.55            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.19/0.55  thf('76', plain,
% 0.19/0.55      ((((sk_D_1)
% 0.19/0.55          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.19/0.55             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['74', '75'])).
% 0.19/0.55  thf(d3_mcart_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.19/0.55  thf('77', plain,
% 0.19/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.55         ((k3_mcart_1 @ X20 @ X21 @ X22)
% 0.19/0.55           = (k4_tarski @ (k4_tarski @ X20 @ X21) @ X22))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.55  thf(t20_mcart_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.55       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.55  thf('78', plain,
% 0.19/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.55         (((X26) != (k2_mcart_1 @ X26)) | ((X26) != (k4_tarski @ X27 @ X28)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.19/0.55  thf('79', plain,
% 0.19/0.55      (![X27 : $i, X28 : $i]:
% 0.19/0.55         ((k4_tarski @ X27 @ X28) != (k2_mcart_1 @ (k4_tarski @ X27 @ X28)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['78'])).
% 0.19/0.55  thf(t7_mcart_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.55       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.55  thf('80', plain,
% 0.19/0.55      (![X41 : $i, X43 : $i]: ((k2_mcart_1 @ (k4_tarski @ X41 @ X43)) = (X43))),
% 0.19/0.55      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.55  thf('81', plain, (![X27 : $i, X28 : $i]: ((k4_tarski @ X27 @ X28) != (X28))),
% 0.19/0.55      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.55  thf('82', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['77', '81'])).
% 0.19/0.55  thf('83', plain,
% 0.19/0.55      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['76', '82'])).
% 0.19/0.55  thf('84', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.19/0.55      inference('clc', [status(thm)], ['6', '18'])).
% 0.19/0.55  thf('85', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['14', '16'])).
% 0.19/0.55  thf('86', plain,
% 0.19/0.55      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.19/0.55         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['45', '46', '47', '48'])).
% 0.19/0.55  thf('87', plain,
% 0.19/0.55      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('split', [status(esa)], ['32'])).
% 0.19/0.55  thf('88', plain,
% 0.19/0.55      ((((sk_D_1) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.19/0.55         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['86', '87'])).
% 0.19/0.55  thf('89', plain,
% 0.19/0.55      (((sk_D_1)
% 0.19/0.55         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.19/0.55            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.19/0.55  thf('90', plain,
% 0.19/0.55      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.55         (((X29) = (k1_xboole_0))
% 0.19/0.55          | ~ (r2_hidden @ X30 @ X29)
% 0.19/0.55          | ((sk_B @ X29) != (k3_mcart_1 @ X31 @ X30 @ X32)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.19/0.55  thf('91', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (((sk_B @ X0) != (sk_D_1))
% 0.19/0.55          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ X0)
% 0.19/0.55          | ((X0) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['89', '90'])).
% 0.19/0.55  thf('92', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          (~ (r2_hidden @ sk_D_1 @ X0)
% 0.19/0.55           | ((X0) = (k1_xboole_0))
% 0.19/0.55           | ((sk_B @ X0) != (sk_D_1))))
% 0.19/0.55         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['88', '91'])).
% 0.19/0.55  thf('93', plain,
% 0.19/0.55      (((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.19/0.55         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.19/0.55         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['85', '92'])).
% 0.19/0.55  thf('94', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.19/0.55      inference('demod', [status(thm)], ['13', '17'])).
% 0.19/0.55  thf('95', plain,
% 0.19/0.55      ((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('clc', [status(thm)], ['93', '94'])).
% 0.19/0.55  thf('96', plain,
% 0.19/0.55      ((((sk_D_1) != (sk_D_1)))
% 0.19/0.55         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['84', '95'])).
% 0.19/0.55  thf('97', plain,
% 0.19/0.55      (~ (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['96'])).
% 0.19/0.55  thf('98', plain,
% 0.19/0.55      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.19/0.55       (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.19/0.55       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.19/0.55      inference('split', [status(esa)], ['32'])).
% 0.19/0.55  thf('99', plain,
% 0.19/0.55      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['83', '97', '98'])).
% 0.19/0.55  thf('100', plain, ($false),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['71', '99'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
