%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cgan8Gl9QA

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 282 expanded)
%              Number of leaves         :   29 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          : 1047 (4277 expanded)
%              Number of equality atoms :  132 ( 598 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X30
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ ( k6_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ ( k7_mcart_1 @ X27 @ X28 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X27 @ X28 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X30
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ ( k6_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ ( k7_mcart_1 @ X27 @ X28 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7','8','9'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_mcart_1 @ X14 @ X15 @ X16 )
      = ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('13',plain,(
    ! [X31: $i,X33: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X31 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_mcart_1 @ sk_D_1 )
    = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('20',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7','8','9'])).

thf('21',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_mcart_1 @ X14 @ X15 @ X16 )
      = ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
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

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k2_mcart_1 @ X20 ) )
      | ( X20
       != ( k4_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_tarski @ X21 @ X22 )
     != ( k2_mcart_1 @ ( k4_tarski @ X21 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X31: $i,X33: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X31 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_tarski @ X21 @ X22 )
     != X22 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('32',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('33',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ sk_D_1 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

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

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ( ( sk_B @ X23 )
       != ( k3_mcart_1 @ X25 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_1 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('38',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ ( k1_tarski @ X13 ) )
        = X12 )
      | ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ ( sk_B @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X12 @ ( k1_tarski @ X11 ) )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('57',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['44','57'])).

thf('59',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('60',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( sk_D_1 != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['36','61'])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_D_1
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('68',plain,
    ( sk_D_1
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['28','66','67'])).

thf('69',plain,
    ( sk_D_1
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['18','68'])).

thf('70',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1 ) @ sk_D_1 @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['16','69'])).

thf('71',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('72',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ( ( sk_B @ X23 )
       != ( k3_mcart_1 @ X25 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('78',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cgan8Gl9QA
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 95 iterations in 0.086s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.54  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(t51_mcart_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ~( ![D:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.54                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.54                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.54                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54             ( ~( ![D:$i]:
% 0.21/0.54                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.54                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.54                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.54                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d3_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.54         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.21/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.54        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf(t48_mcart_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ~( ![D:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.54                 ( ( D ) =
% 0.21/0.54                   ( k3_mcart_1 @
% 0.21/0.54                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.54                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.54                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.54         (((X27) = (k1_xboole_0))
% 0.21/0.54          | ((X28) = (k1_xboole_0))
% 0.21/0.54          | ((X30)
% 0.21/0.54              = (k3_mcart_1 @ (k5_mcart_1 @ X27 @ X28 @ X29 @ X30) @ 
% 0.21/0.54                 (k6_mcart_1 @ X27 @ X28 @ X29 @ X30) @ 
% 0.21/0.54                 (k7_mcart_1 @ X27 @ X28 @ X29 @ X30)))
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k3_zfmisc_1 @ X27 @ X28 @ X29))
% 0.21/0.54          | ((X29) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.54         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.21/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.54         (((X27) = (k1_xboole_0))
% 0.21/0.54          | ((X28) = (k1_xboole_0))
% 0.21/0.54          | ((X30)
% 0.21/0.54              = (k3_mcart_1 @ (k5_mcart_1 @ X27 @ X28 @ X29 @ X30) @ 
% 0.21/0.54                 (k6_mcart_1 @ X27 @ X28 @ X29 @ X30) @ 
% 0.21/0.54                 (k7_mcart_1 @ X27 @ X28 @ X29 @ X30)))
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ 
% 0.21/0.54               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))
% 0.21/0.54          | ((X29) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.54        | ((sk_D_1)
% 0.21/0.54            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.21/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.54  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('9', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (((sk_D_1)
% 0.21/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['6', '7', '8', '9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (((sk_D_1)
% 0.21/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['6', '7', '8', '9'])).
% 0.21/0.54  thf(d3_mcart_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.54         ((k3_mcart_1 @ X14 @ X15 @ X16)
% 0.21/0.54           = (k4_tarski @ (k4_tarski @ X14 @ X15) @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.54  thf(t7_mcart_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.54       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X31 : $i, X33 : $i]: ((k2_mcart_1 @ (k4_tarski @ X31 @ X33)) = (X33))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (((k2_mcart_1 @ sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['11', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (((sk_D_1)
% 0.21/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k2_mcart_1 @ sk_D_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))
% 0.21/0.54        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))
% 0.21/0.54        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.21/0.54         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.21/0.54         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['17'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (((sk_D_1)
% 0.21/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['6', '7', '8', '9'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      ((((sk_D_1)
% 0.21/0.54          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ sk_D_1)))
% 0.21/0.54         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.54         ((k3_mcart_1 @ X14 @ X15 @ X16)
% 0.21/0.54           = (k4_tarski @ (k4_tarski @ X14 @ X15) @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.54  thf(t20_mcart_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.54       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (((X20) != (k2_mcart_1 @ X20)) | ((X20) != (k4_tarski @ X21 @ X22)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i]:
% 0.21/0.54         ((k4_tarski @ X21 @ X22) != (k2_mcart_1 @ (k4_tarski @ X21 @ X22)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X31 : $i, X33 : $i]: ((k2_mcart_1 @ (k4_tarski @ X31 @ X33)) = (X33))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.54  thf('26', plain, (![X21 : $i, X22 : $i]: ((k4_tarski @ X21 @ X22) != (X22))),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['21', '27'])).
% 0.21/0.54  thf(d1_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.54         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.54  thf('30', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))
% 0.21/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['17'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (((sk_D_1)
% 0.21/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            (k2_mcart_1 @ sk_D_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((((sk_D_1)
% 0.21/0.54          = (k3_mcart_1 @ sk_D_1 @ 
% 0.21/0.54             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54             (k2_mcart_1 @ sk_D_1))))
% 0.21/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf(t29_mcart_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.54                 ( ![C:$i,D:$i,E:$i]:
% 0.21/0.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.54                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.54         (((X23) = (k1_xboole_0))
% 0.21/0.54          | ~ (r2_hidden @ X25 @ X23)
% 0.21/0.54          | ((sk_B @ X23) != (k3_mcart_1 @ X25 @ X24 @ X26)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (((sk_B @ X0) != (sk_D_1))
% 0.21/0.54           | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.21/0.54           | ((X0) = (k1_xboole_0))))
% 0.21/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.21/0.54         | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))))
% 0.21/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '35'])).
% 0.21/0.54  thf('37', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X23 : $i]:
% 0.21/0.54         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.54  thf(t65_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]:
% 0.21/0.54         (((k4_xboole_0 @ X12 @ (k1_tarski @ X13)) = (X12))
% 0.21/0.54          | (r2_hidden @ X13 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.54  thf(d5_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.54          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.54          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.54          | (r2_hidden @ X1 @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.54          | (r2_hidden @ X0 @ X1)
% 0.21/0.54          | ~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ X0 @ (k1_tarski @ (sk_B @ (k1_tarski @ X0))))
% 0.21/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X23 : $i]:
% 0.21/0.54         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.54          | (r2_hidden @ X4 @ X1)
% 0.21/0.54          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.54         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X23 : $i]:
% 0.21/0.54         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.54          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.21/0.54          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.54  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X11 @ X12)
% 0.21/0.54          | ((k4_xboole_0 @ X12 @ (k1_tarski @ X11)) != (X12)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf('57', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ (sk_B @ (k1_tarski @ X0))))),
% 0.21/0.54      inference('clc', [status(thm)], ['44', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X6 : $i, X9 : $i]:
% 0.21/0.54         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.54  thf('61', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '60'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (((((k1_tarski @ sk_D_1) = (k1_xboole_0)) | ((sk_D_1) != (sk_D_1))))
% 0.21/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('demod', [status(thm)], ['36', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)))
% 0.21/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.54  thf('64', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.54         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (~ (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))) | 
% 0.21/0.54       (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))) | 
% 0.21/0.54       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['17'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['28', '66', '67'])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['18', '68'])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (((sk_D_1)
% 0.21/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D_1) @ 
% 0.21/0.54            sk_D_1 @ (k2_mcart_1 @ sk_D_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '69'])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      (![X23 : $i]:
% 0.21/0.54         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (![X6 : $i, X9 : $i]:
% 0.21/0.54         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.54          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.54         (((X23) = (k1_xboole_0))
% 0.21/0.54          | ~ (r2_hidden @ X24 @ X23)
% 0.21/0.54          | ((sk_B @ X23) != (k3_mcart_1 @ X25 @ X24 @ X26)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.21/0.54          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.21/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))
% 0.21/0.54          | ((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.54  thf('77', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('79', plain, (~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['70', '78'])).
% 0.21/0.54  thf('80', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf('81', plain, ($false), inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
