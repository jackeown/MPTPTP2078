%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6VZZZ7qpK0

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 533 expanded)
%              Number of leaves         :   23 ( 159 expanded)
%              Depth                    :   16
%              Number of atoms          : 1029 (15291 expanded)
%              Number of equality atoms :  114 (2000 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t61_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ~ ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
               => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                  & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                  & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                    = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                  & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                    = ( k2_mcart_1 @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X25
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k10_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k11_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('2',plain,
    ( ( sk_D_2 = k1_xboole_0 )
    | ( sk_E
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ) )
    | ( sk_C_2 = k1_xboole_0 )
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

thf('6',plain,(
    sk_D_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_mcart_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k3_mcart_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

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

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k2_mcart_1 @ X8 ) )
      | ( X11 = X12 )
      | ( X8
       != ( k4_tarski @ X13 @ X12 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_mcart_1])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ X13 @ X12 )
       != ( k4_tarski @ X9 @ X10 ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X12 ) )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( k2_mcart_1 @ sk_E )
    = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_mcart_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k3_mcart_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

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

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4
       != ( k1_mcart_1 @ X1 ) )
      | ( X4 = X5 )
      | ( X1
       != ( k4_tarski @ X5 @ X6 ) )
      | ( X1
       != ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ X5 @ X6 )
       != ( k4_tarski @ X2 @ X3 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_mcart_1 @ X14 @ X15 @ X16 )
      = ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['11'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_mcart_1 @ X14 @ X15 @ X16 )
      = ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('34',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['11'])).

thf('37',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( k2_mcart_1 @ sk_E )
    = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('41',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ sk_E ) )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['38'])).

thf('42',plain,
    ( ( ( k2_mcart_1 @ sk_E )
     != ( k2_mcart_1 @ sk_E ) )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('45',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('46',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('49',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('50',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['38'])).

thf('53',plain,(
    ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference('sat_resolution*',[status(thm)],['43','47','51','52'])).

thf('54',plain,(
    ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 @ sk_E )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(simpl_trail,[status(thm)],['39','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','54'])).


%------------------------------------------------------------------------------
