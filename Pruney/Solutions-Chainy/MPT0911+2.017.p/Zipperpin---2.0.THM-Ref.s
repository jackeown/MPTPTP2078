%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oWsfyjGoV0

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:58 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  244 (1098 expanded)
%              Number of leaves         :   39 ( 351 expanded)
%              Depth                    :   32
%              Number of atoms          : 2228 (15740 expanded)
%              Number of equality atoms :  314 (2170 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('sup-',[status(thm)],['2','5'])).

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

thf('7',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ( X35 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X37 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('14',plain,(
    ! [X33: $i,X34: $i,X37: $i] :
      ( ( k4_zfmisc_1 @ X33 @ X34 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ( X37 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X37 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference(demod,[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
       != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( k1_xboole_0 != sk_E_1 )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
        = sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('36',plain,
    ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
    = sk_E_1 ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
    = sk_E_1 ),
    inference(clc,[status(thm)],['34','35'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('38',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X38 @ X39 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('39',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( sk_D @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
    = sk_E_1 ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
    = sk_E_1 ),
    inference(demod,[status(thm)],['36','39'])).

thf('42',plain,(
    ! [X38: $i,X40: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X38 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('43',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_E @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) )
    = sk_E_1 ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('53',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X38 @ X39 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('54',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('56',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
       != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64','65','66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('70',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('71',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['51','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('74',plain,(
    ! [X38: $i,X40: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X38 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('75',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('77',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
       != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
        = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('92',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['72','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('95',plain,
    ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
       != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['102','103','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['102','103','104','105'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    = ( k1_mcart_1 @ sk_E_1 ) ),
    inference(condensation,[status(thm)],['109'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('111',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_mcart_1 @ X11 @ X12 @ X13 )
      = ( k4_tarski @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('114',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X21 ) @ X23 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('117',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
       != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
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
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
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
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['124','125','126','127'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('129',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('134',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ sk_B_2 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X42 @ X41 @ X43 ) )
      | ( sk_D_1 = X43 )
      | ~ ( m1_subset_1 @ X43 @ sk_C )
      | ~ ( m1_subset_1 @ X42 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_1 = X1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('139',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('142',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
       != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['149','150','151','152'])).

thf('154',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('159',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','159'])).

thf('161',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['44','160'])).

thf('162',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('163',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('168',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('169',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X21 ) @ X23 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['167','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('173',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
       != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['177','178','179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['166','181'])).

thf('183',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('191',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['161','191'])).

thf('193',plain,
    ( sk_D_1
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('196',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X29 @ X30 @ X32 @ X31 )
        = ( k2_mcart_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('197',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['197','198','199','200'])).

thf('202',plain,(
    sk_D_1
 != ( k2_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['194','201'])).

thf('203',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['193','202'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oWsfyjGoV0
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.92/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.92/1.14  % Solved by: fo/fo7.sh
% 0.92/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.14  % done 791 iterations in 0.680s
% 0.92/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.92/1.14  % SZS output start Refutation
% 0.92/1.14  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.92/1.14  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.92/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.92/1.14  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.92/1.14  thf(sk_E_type, type, sk_E: $i > $i).
% 0.92/1.14  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.92/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.92/1.14  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.92/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.92/1.14  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.92/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.14  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.92/1.14  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.92/1.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.92/1.14  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.92/1.14  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.92/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.14  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.92/1.14  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.92/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.92/1.14  thf(sk_D_type, type, sk_D: $i > $i).
% 0.92/1.14  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.92/1.14  thf(t71_mcart_1, conjecture,
% 0.92/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.92/1.14     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.92/1.14       ( ( ![F:$i]:
% 0.92/1.14           ( ( m1_subset_1 @ F @ A ) =>
% 0.92/1.14             ( ![G:$i]:
% 0.92/1.14               ( ( m1_subset_1 @ G @ B ) =>
% 0.92/1.14                 ( ![H:$i]:
% 0.92/1.14                   ( ( m1_subset_1 @ H @ C ) =>
% 0.92/1.14                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.92/1.14                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.92/1.14         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.14           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.92/1.14           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.92/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.14    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.92/1.14        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.92/1.14          ( ( ![F:$i]:
% 0.92/1.14              ( ( m1_subset_1 @ F @ A ) =>
% 0.92/1.14                ( ![G:$i]:
% 0.92/1.14                  ( ( m1_subset_1 @ G @ B ) =>
% 0.92/1.14                    ( ![H:$i]:
% 0.92/1.14                      ( ( m1_subset_1 @ H @ C ) =>
% 0.92/1.14                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.92/1.14                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.92/1.14            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.14              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.92/1.14              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.92/1.14    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.92/1.14  thf('0', plain,
% 0.92/1.14      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf(t2_subset, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( m1_subset_1 @ A @ B ) =>
% 0.92/1.14       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.92/1.14  thf('1', plain,
% 0.92/1.14      (![X9 : $i, X10 : $i]:
% 0.92/1.14         ((r2_hidden @ X9 @ X10)
% 0.92/1.14          | (v1_xboole_0 @ X10)
% 0.92/1.14          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.92/1.14      inference('cnf', [status(esa)], [t2_subset])).
% 0.92/1.14  thf('2', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.92/1.14  thf(d3_zfmisc_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.92/1.14       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.92/1.14  thf('3', plain,
% 0.92/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.92/1.14         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 0.92/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.92/1.14  thf(l139_zfmisc_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.92/1.14          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.92/1.14  thf('4', plain,
% 0.92/1.14      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.92/1.14         (((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3))
% 0.92/1.14          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.92/1.14      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.92/1.14  thf('5', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.92/1.14          | ((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['3', '4'])).
% 0.92/1.14  thf('6', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['2', '5'])).
% 0.92/1.14  thf(t34_mcart_1, axiom,
% 0.92/1.14    (![A:$i]:
% 0.92/1.14     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.92/1.14          ( ![B:$i]:
% 0.92/1.14            ( ~( ( r2_hidden @ B @ A ) & 
% 0.92/1.14                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.92/1.14                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.92/1.14                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.92/1.14  thf('7', plain,
% 0.92/1.14      (![X24 : $i]:
% 0.92/1.14         (((X24) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X24) @ X24))),
% 0.92/1.14      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.92/1.14  thf(d1_xboole_0, axiom,
% 0.92/1.14    (![A:$i]:
% 0.92/1.14     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.92/1.14  thf('8', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.92/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.92/1.14  thf('9', plain,
% 0.92/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.14  thf('10', plain,
% 0.92/1.14      ((((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 0.92/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['6', '9'])).
% 0.92/1.14  thf(d4_zfmisc_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.92/1.14     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.92/1.14       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.92/1.14  thf('11', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('12', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.92/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.92/1.14          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 0.92/1.14      inference('sup+', [status(thm)], ['10', '11'])).
% 0.92/1.14  thf(t55_mcart_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.92/1.14     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.92/1.14         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.92/1.14       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.92/1.14  thf('13', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 0.92/1.14         (((X35) != (k1_xboole_0))
% 0.92/1.14          | ((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X37) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('14', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X37 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X33 @ X34 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.92/1.14      inference('simplify', [status(thm)], ['13'])).
% 0.92/1.14  thf('15', plain,
% 0.92/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.92/1.14         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 0.92/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.92/1.14  thf('16', plain,
% 0.92/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.92/1.14         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 0.92/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.92/1.14  thf('17', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.92/1.14      inference('sup+', [status(thm)], ['15', '16'])).
% 0.92/1.14  thf('18', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('19', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.92/1.14           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.92/1.14      inference('demod', [status(thm)], ['17', '18'])).
% 0.92/1.14  thf('20', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('21', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 0.92/1.14           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.92/1.14      inference('sup+', [status(thm)], ['19', '20'])).
% 0.92/1.14  thf('22', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         ((k1_xboole_0)
% 0.92/1.14           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 0.92/1.14      inference('sup+', [status(thm)], ['14', '21'])).
% 0.92/1.14  thf('23', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 0.92/1.14         (((X37) != (k1_xboole_0))
% 0.92/1.14          | ((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X37) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('24', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X33 @ X34 @ X35 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.14      inference('simplify', [status(thm)], ['23'])).
% 0.92/1.14  thf('25', plain,
% 0.92/1.14      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.92/1.14      inference('demod', [status(thm)], ['22', '24'])).
% 0.92/1.14  thf('26', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 0.92/1.14      inference('demod', [status(thm)], ['12', '25'])).
% 0.92/1.14  thf('27', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36) != (k1_xboole_0))
% 0.92/1.14          | ((X36) = (k1_xboole_0))
% 0.92/1.14          | ((X35) = (k1_xboole_0))
% 0.92/1.14          | ((X34) = (k1_xboole_0))
% 0.92/1.14          | ((X33) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('28', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['26', '27'])).
% 0.92/1.14  thf('29', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 0.92/1.14      inference('simplify', [status(thm)], ['28'])).
% 0.92/1.14  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('31', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('33', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.92/1.14  thf('34', plain,
% 0.92/1.14      ((((k1_xboole_0) != (sk_E_1))
% 0.92/1.14        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 0.92/1.14      inference('eq_fact', [status(thm)], ['33'])).
% 0.92/1.14  thf('35', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.92/1.14  thf('36', plain,
% 0.92/1.14      (((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))),
% 0.92/1.14      inference('clc', [status(thm)], ['34', '35'])).
% 0.92/1.14  thf('37', plain,
% 0.92/1.14      (((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))),
% 0.92/1.14      inference('clc', [status(thm)], ['34', '35'])).
% 0.92/1.14  thf(t7_mcart_1, axiom,
% 0.92/1.14    (![A:$i,B:$i]:
% 0.92/1.14     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.92/1.14       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.92/1.14  thf('38', plain,
% 0.92/1.14      (![X38 : $i, X39 : $i]: ((k1_mcart_1 @ (k4_tarski @ X38 @ X39)) = (X38))),
% 0.92/1.14      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.92/1.14  thf('39', plain, (((k1_mcart_1 @ sk_E_1) = (sk_D @ sk_E_1))),
% 0.92/1.14      inference('sup+', [status(thm)], ['37', '38'])).
% 0.92/1.14  thf('40', plain,
% 0.92/1.14      (((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))),
% 0.92/1.14      inference('demod', [status(thm)], ['36', '39'])).
% 0.92/1.14  thf('41', plain,
% 0.92/1.14      (((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))),
% 0.92/1.14      inference('demod', [status(thm)], ['36', '39'])).
% 0.92/1.14  thf('42', plain,
% 0.92/1.14      (![X38 : $i, X40 : $i]: ((k2_mcart_1 @ (k4_tarski @ X38 @ X40)) = (X40))),
% 0.92/1.14      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.92/1.14  thf('43', plain, (((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))),
% 0.92/1.14      inference('sup+', [status(thm)], ['41', '42'])).
% 0.92/1.14  thf('44', plain,
% 0.92/1.14      (((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)) = (sk_E_1))),
% 0.92/1.14      inference('demod', [status(thm)], ['40', '43'])).
% 0.92/1.14  thf('45', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.92/1.14  thf('46', plain,
% 0.92/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.92/1.14         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 0.92/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.92/1.14  thf(t10_mcart_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.92/1.14       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.92/1.14         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.92/1.14  thf('47', plain,
% 0.92/1.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.14         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 0.92/1.14          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.92/1.14  thf('48', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.92/1.14          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['46', '47'])).
% 0.92/1.14  thf('49', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['45', '48'])).
% 0.92/1.14  thf('50', plain,
% 0.92/1.14      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.92/1.14         (((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3))
% 0.92/1.14          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.92/1.14      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.92/1.14  thf('51', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | ((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.92/1.14  thf('52', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | ((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.92/1.14  thf('53', plain,
% 0.92/1.14      (![X38 : $i, X39 : $i]: ((k1_mcart_1 @ (k4_tarski @ X38 @ X39)) = (X38))),
% 0.92/1.14      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.92/1.14  thf('54', plain,
% 0.92/1.14      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 0.92/1.14        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.92/1.14      inference('sup+', [status(thm)], ['52', '53'])).
% 0.92/1.14  thf('55', plain,
% 0.92/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.14  thf('56', plain,
% 0.92/1.14      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 0.92/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['54', '55'])).
% 0.92/1.14  thf('57', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('58', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.92/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.92/1.14          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('sup+', [status(thm)], ['56', '57'])).
% 0.92/1.14  thf('59', plain,
% 0.92/1.14      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.92/1.14      inference('demod', [status(thm)], ['22', '24'])).
% 0.92/1.14  thf('60', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.92/1.14          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('demod', [status(thm)], ['58', '59'])).
% 0.92/1.14  thf('61', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36) != (k1_xboole_0))
% 0.92/1.14          | ((X36) = (k1_xboole_0))
% 0.92/1.14          | ((X35) = (k1_xboole_0))
% 0.92/1.14          | ((X34) = (k1_xboole_0))
% 0.92/1.14          | ((X33) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('62', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.14          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['60', '61'])).
% 0.92/1.14  thf('63', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('simplify', [status(thm)], ['62'])).
% 0.92/1.14  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('65', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('66', plain, (((sk_C) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('67', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)], ['63', '64', '65', '66'])).
% 0.92/1.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.92/1.14  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.14  thf('69', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         ((v1_xboole_0 @ X0)
% 0.92/1.14          | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('sup+', [status(thm)], ['67', '68'])).
% 0.92/1.14  thf(fc1_subset_1, axiom,
% 0.92/1.14    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.92/1.14  thf('70', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.92/1.14  thf('71', plain,
% 0.92/1.14      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['69', '70'])).
% 0.92/1.14  thf('72', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('demod', [status(thm)], ['51', '71'])).
% 0.92/1.14  thf('73', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | ((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.92/1.14  thf('74', plain,
% 0.92/1.14      (![X38 : $i, X40 : $i]: ((k2_mcart_1 @ (k4_tarski @ X38 @ X40)) = (X40))),
% 0.92/1.14      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.92/1.14  thf('75', plain,
% 0.92/1.14      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 0.92/1.14        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.92/1.14      inference('sup+', [status(thm)], ['73', '74'])).
% 0.92/1.14  thf('76', plain,
% 0.92/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.14  thf('77', plain,
% 0.92/1.14      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 0.92/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['75', '76'])).
% 0.92/1.14  thf('78', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('79', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.92/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.92/1.14          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('sup+', [status(thm)], ['77', '78'])).
% 0.92/1.14  thf('80', plain,
% 0.92/1.14      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.92/1.14      inference('demod', [status(thm)], ['22', '24'])).
% 0.92/1.14  thf('81', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.92/1.14          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('demod', [status(thm)], ['79', '80'])).
% 0.92/1.14  thf('82', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36) != (k1_xboole_0))
% 0.92/1.14          | ((X36) = (k1_xboole_0))
% 0.92/1.14          | ((X35) = (k1_xboole_0))
% 0.92/1.14          | ((X34) = (k1_xboole_0))
% 0.92/1.14          | ((X33) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('83', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.14          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['81', '82'])).
% 0.92/1.14  thf('84', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('simplify', [status(thm)], ['83'])).
% 0.92/1.14  thf('85', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('86', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('87', plain, (((sk_C) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('88', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)], ['84', '85', '86', '87'])).
% 0.92/1.14  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.14  thf('90', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         ((v1_xboole_0 @ X0)
% 0.92/1.14          | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 0.92/1.14              = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 0.92/1.14      inference('sup+', [status(thm)], ['88', '89'])).
% 0.92/1.14  thf('91', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.92/1.14  thf('92', plain,
% 0.92/1.14      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['90', '91'])).
% 0.92/1.14  thf('93', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('demod', [status(thm)], ['72', '92'])).
% 0.92/1.14  thf('94', plain,
% 0.92/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.14  thf('95', plain,
% 0.92/1.14      ((((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14          (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 0.92/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['93', '94'])).
% 0.92/1.14  thf('96', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('97', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.92/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.92/1.14          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('sup+', [status(thm)], ['95', '96'])).
% 0.92/1.14  thf('98', plain,
% 0.92/1.14      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.92/1.14      inference('demod', [status(thm)], ['22', '24'])).
% 0.92/1.14  thf('99', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('demod', [status(thm)], ['97', '98'])).
% 0.92/1.14  thf('100', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36) != (k1_xboole_0))
% 0.92/1.14          | ((X36) = (k1_xboole_0))
% 0.92/1.14          | ((X35) = (k1_xboole_0))
% 0.92/1.14          | ((X34) = (k1_xboole_0))
% 0.92/1.14          | ((X33) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('101', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['99', '100'])).
% 0.92/1.14  thf('102', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('simplify', [status(thm)], ['101'])).
% 0.92/1.14  thf('103', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('104', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('105', plain, (((sk_C) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('106', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)],
% 0.92/1.14                ['102', '103', '104', '105'])).
% 0.92/1.14  thf('107', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)],
% 0.92/1.14                ['102', '103', '104', '105'])).
% 0.92/1.14  thf('108', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (((X1) = (X0))
% 0.92/1.14          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 0.92/1.14          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('sup+', [status(thm)], ['106', '107'])).
% 0.92/1.14  thf('109', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 0.92/1.14          | ((X1) = (X0)))),
% 0.92/1.14      inference('simplify', [status(thm)], ['108'])).
% 0.92/1.14  thf('110', plain,
% 0.92/1.14      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14         (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))),
% 0.92/1.14      inference('condensation', [status(thm)], ['109'])).
% 0.92/1.14  thf(d3_mcart_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.92/1.14  thf('111', plain,
% 0.92/1.14      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.92/1.14         ((k3_mcart_1 @ X11 @ X12 @ X13)
% 0.92/1.14           = (k4_tarski @ (k4_tarski @ X11 @ X12) @ X13))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.92/1.14  thf('112', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.92/1.14           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 0.92/1.14           = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))),
% 0.92/1.14      inference('sup+', [status(thm)], ['110', '111'])).
% 0.92/1.14  thf('113', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['45', '48'])).
% 0.92/1.14  thf('114', plain,
% 0.92/1.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.14         ((r2_hidden @ (k2_mcart_1 @ X21) @ X23)
% 0.92/1.14          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.92/1.14  thf('115', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 0.92/1.14      inference('sup-', [status(thm)], ['113', '114'])).
% 0.92/1.14  thf('116', plain,
% 0.92/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.14  thf('117', plain,
% 0.92/1.14      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 0.92/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['115', '116'])).
% 0.92/1.14  thf('118', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('119', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.92/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 0.92/1.14      inference('sup+', [status(thm)], ['117', '118'])).
% 0.92/1.14  thf('120', plain,
% 0.92/1.14      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.92/1.14      inference('demod', [status(thm)], ['22', '24'])).
% 0.92/1.14  thf('121', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 0.92/1.14      inference('demod', [status(thm)], ['119', '120'])).
% 0.92/1.14  thf('122', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36) != (k1_xboole_0))
% 0.92/1.14          | ((X36) = (k1_xboole_0))
% 0.92/1.14          | ((X35) = (k1_xboole_0))
% 0.92/1.14          | ((X34) = (k1_xboole_0))
% 0.92/1.14          | ((X33) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('123', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['121', '122'])).
% 0.92/1.14  thf('124', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 0.92/1.14      inference('simplify', [status(thm)], ['123'])).
% 0.92/1.14  thf('125', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('126', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('127', plain, (((sk_C) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('128', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)],
% 0.92/1.14                ['124', '125', '126', '127'])).
% 0.92/1.14  thf(t1_subset, axiom,
% 0.92/1.14    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.92/1.14  thf('129', plain,
% 0.92/1.14      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.92/1.14      inference('cnf', [status(esa)], [t1_subset])).
% 0.92/1.14  thf('130', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 0.92/1.14      inference('sup-', [status(thm)], ['128', '129'])).
% 0.92/1.14  thf('131', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.14  thf('132', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         ((v1_xboole_0 @ X0)
% 0.92/1.14          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 0.92/1.14      inference('sup+', [status(thm)], ['130', '131'])).
% 0.92/1.14  thf('133', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.92/1.14  thf('134', plain,
% 0.92/1.14      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)),
% 0.92/1.14      inference('sup-', [status(thm)], ['132', '133'])).
% 0.92/1.14  thf('135', plain,
% 0.92/1.14      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.92/1.14         (~ (m1_subset_1 @ X41 @ sk_B_2)
% 0.92/1.14          | ((sk_E_1) != (k3_mcart_1 @ X42 @ X41 @ X43))
% 0.92/1.14          | ((sk_D_1) = (X43))
% 0.92/1.14          | ~ (m1_subset_1 @ X43 @ sk_C)
% 0.92/1.14          | ~ (m1_subset_1 @ X42 @ sk_A))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('136', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.92/1.14          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.92/1.14          | ((sk_D_1) = (X1))
% 0.92/1.14          | ((sk_E_1)
% 0.92/1.14              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['134', '135'])).
% 0.92/1.14  thf('137', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 0.92/1.14          | ((sk_D_1) = (X0))
% 0.92/1.14          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.92/1.14          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.92/1.14      inference('sup-', [status(thm)], ['112', '136'])).
% 0.92/1.14  thf('138', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['45', '48'])).
% 0.92/1.14  thf('139', plain,
% 0.92/1.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.14         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 0.92/1.14          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.92/1.14  thf('140', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.92/1.14      inference('sup-', [status(thm)], ['138', '139'])).
% 0.92/1.14  thf('141', plain,
% 0.92/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.14  thf('142', plain,
% 0.92/1.14      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 0.92/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['140', '141'])).
% 0.92/1.14  thf('143', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('144', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.92/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.92/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.92/1.14      inference('sup+', [status(thm)], ['142', '143'])).
% 0.92/1.14  thf('145', plain,
% 0.92/1.14      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.92/1.14      inference('demod', [status(thm)], ['22', '24'])).
% 0.92/1.14  thf('146', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.92/1.14      inference('demod', [status(thm)], ['144', '145'])).
% 0.92/1.14  thf('147', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36) != (k1_xboole_0))
% 0.92/1.14          | ((X36) = (k1_xboole_0))
% 0.92/1.14          | ((X35) = (k1_xboole_0))
% 0.92/1.14          | ((X34) = (k1_xboole_0))
% 0.92/1.14          | ((X33) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('148', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['146', '147'])).
% 0.92/1.14  thf('149', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.92/1.14      inference('simplify', [status(thm)], ['148'])).
% 0.92/1.14  thf('150', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('151', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('152', plain, (((sk_C) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('153', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)],
% 0.92/1.14                ['149', '150', '151', '152'])).
% 0.92/1.14  thf('154', plain,
% 0.92/1.14      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.92/1.14      inference('cnf', [status(esa)], [t1_subset])).
% 0.92/1.14  thf('155', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0))
% 0.92/1.14          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.92/1.14      inference('sup-', [status(thm)], ['153', '154'])).
% 0.92/1.14  thf('156', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.14  thf('157', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         ((v1_xboole_0 @ X0)
% 0.92/1.14          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.92/1.14      inference('sup+', [status(thm)], ['155', '156'])).
% 0.92/1.14  thf('158', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.92/1.14  thf('159', plain,
% 0.92/1.14      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)),
% 0.92/1.14      inference('sup-', [status(thm)], ['157', '158'])).
% 0.92/1.14  thf('160', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 0.92/1.14          | ((sk_D_1) = (X0))
% 0.92/1.14          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.92/1.14      inference('demod', [status(thm)], ['137', '159'])).
% 0.92/1.14  thf('161', plain,
% 0.92/1.14      ((((sk_E_1) != (sk_E_1))
% 0.92/1.14        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 0.92/1.14        | ((sk_D_1) = (k2_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['44', '160'])).
% 0.92/1.14  thf('162', plain,
% 0.92/1.14      (![X24 : $i]:
% 0.92/1.14         (((X24) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X24) @ X24))),
% 0.92/1.14      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.92/1.14  thf('163', plain,
% 0.92/1.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.14         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 0.92/1.14          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.92/1.14  thf('164', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.92/1.14      inference('sup-', [status(thm)], ['162', '163'])).
% 0.92/1.14  thf('165', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.92/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.92/1.14  thf('166', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i]:
% 0.92/1.14         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['164', '165'])).
% 0.92/1.14  thf('167', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.92/1.14  thf('168', plain,
% 0.92/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.92/1.14         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 0.92/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 0.92/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.92/1.14  thf('169', plain,
% 0.92/1.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.14         ((r2_hidden @ (k2_mcart_1 @ X21) @ X23)
% 0.92/1.14          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.92/1.14  thf('170', plain,
% 0.92/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.14         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['168', '169'])).
% 0.92/1.14  thf('171', plain,
% 0.92/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.92/1.14        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 0.92/1.14      inference('sup-', [status(thm)], ['167', '170'])).
% 0.92/1.14  thf('172', plain,
% 0.92/1.14      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.14  thf('173', plain,
% 0.92/1.14      (((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 0.92/1.14        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['171', '172'])).
% 0.92/1.14  thf('174', plain,
% 0.92/1.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.14         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 0.92/1.14           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 0.92/1.14      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.92/1.14  thf('175', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.92/1.14            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 0.92/1.14      inference('sup+', [status(thm)], ['173', '174'])).
% 0.92/1.14  thf('176', plain,
% 0.92/1.14      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.92/1.14         (((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36) != (k1_xboole_0))
% 0.92/1.14          | ((X36) = (k1_xboole_0))
% 0.92/1.14          | ((X35) = (k1_xboole_0))
% 0.92/1.14          | ((X34) = (k1_xboole_0))
% 0.92/1.14          | ((X33) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.92/1.14  thf('177', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 0.92/1.14          | ((sk_A) = (k1_xboole_0))
% 0.92/1.14          | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14          | ((sk_C) = (k1_xboole_0))
% 0.92/1.14          | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['175', '176'])).
% 0.92/1.14  thf('178', plain, (((sk_C) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('179', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('180', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('181', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 0.92/1.14          | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)],
% 0.92/1.14                ['177', '178', '179', '180'])).
% 0.92/1.14  thf('182', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.14          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.92/1.14          | ((X0) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 0.92/1.14      inference('sup-', [status(thm)], ['166', '181'])).
% 0.92/1.14  thf('183', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.14  thf('184', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.14          | ((X0) = (k1_xboole_0))
% 0.92/1.14          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 0.92/1.14      inference('demod', [status(thm)], ['182', '183'])).
% 0.92/1.14  thf('185', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         ((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C) | ((X0) = (k1_xboole_0)))),
% 0.92/1.14      inference('simplify', [status(thm)], ['184'])).
% 0.92/1.14  thf('186', plain,
% 0.92/1.14      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.92/1.14      inference('cnf', [status(esa)], [t1_subset])).
% 0.92/1.14  thf('187', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 0.92/1.14      inference('sup-', [status(thm)], ['185', '186'])).
% 0.92/1.14  thf('188', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.14  thf('189', plain,
% 0.92/1.14      (![X0 : $i]:
% 0.92/1.14         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 0.92/1.14      inference('sup+', [status(thm)], ['187', '188'])).
% 0.92/1.14  thf('190', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.92/1.14      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.92/1.14  thf('191', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C)),
% 0.92/1.14      inference('sup-', [status(thm)], ['189', '190'])).
% 0.92/1.14  thf('192', plain,
% 0.92/1.14      ((((sk_E_1) != (sk_E_1)) | ((sk_D_1) = (k2_mcart_1 @ sk_E_1)))),
% 0.92/1.14      inference('demod', [status(thm)], ['161', '191'])).
% 0.92/1.14  thf('193', plain, (((sk_D_1) = (k2_mcart_1 @ sk_E_1))),
% 0.92/1.14      inference('simplify', [status(thm)], ['192'])).
% 0.92/1.14  thf('194', plain,
% 0.92/1.14      (((sk_D_1) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('195', plain,
% 0.92/1.14      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf(t50_mcart_1, axiom,
% 0.92/1.14    (![A:$i,B:$i,C:$i]:
% 0.92/1.14     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.92/1.14          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.92/1.14          ( ~( ![D:$i]:
% 0.92/1.14               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.92/1.14                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.92/1.14                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.92/1.14                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.92/1.14                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.92/1.14                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.92/1.14  thf('196', plain,
% 0.92/1.14      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.92/1.14         (((X29) = (k1_xboole_0))
% 0.92/1.14          | ((X30) = (k1_xboole_0))
% 0.92/1.14          | ((k7_mcart_1 @ X29 @ X30 @ X32 @ X31) = (k2_mcart_1 @ X31))
% 0.92/1.14          | ~ (m1_subset_1 @ X31 @ (k3_zfmisc_1 @ X29 @ X30 @ X32))
% 0.92/1.14          | ((X32) = (k1_xboole_0)))),
% 0.92/1.14      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.92/1.14  thf('197', plain,
% 0.92/1.14      ((((sk_C) = (k1_xboole_0))
% 0.92/1.14        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))
% 0.92/1.14        | ((sk_B_2) = (k1_xboole_0))
% 0.92/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.92/1.14      inference('sup-', [status(thm)], ['195', '196'])).
% 0.92/1.14  thf('198', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('199', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('200', plain, (((sk_C) != (k1_xboole_0))),
% 0.92/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.14  thf('201', plain,
% 0.92/1.14      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)],
% 0.92/1.14                ['197', '198', '199', '200'])).
% 0.92/1.14  thf('202', plain, (((sk_D_1) != (k2_mcart_1 @ sk_E_1))),
% 0.92/1.14      inference('demod', [status(thm)], ['194', '201'])).
% 0.92/1.14  thf('203', plain, ($false),
% 0.92/1.14      inference('simplify_reflect-', [status(thm)], ['193', '202'])).
% 0.92/1.14  
% 0.92/1.14  % SZS output end Refutation
% 0.92/1.14  
% 0.92/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
