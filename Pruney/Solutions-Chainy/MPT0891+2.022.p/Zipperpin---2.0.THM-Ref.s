%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sBaAmqG35l

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:36 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 296 expanded)
%              Number of leaves         :   27 (  91 expanded)
%              Depth                    :   26
%              Number of atoms          : 1446 (4104 expanded)
%              Number of equality atoms :  190 ( 549 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X15 @ X17 ) @ X18 )
        = ( k2_tarski @ X15 @ X17 ) )
      | ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) )
        = X13 )
      | ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X15 @ X17 ) @ X16 )
       != ( k2_tarski @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_tarski @ ( sk_B_1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( X1
        = ( sk_B_1 @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['11'])).

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

thf('13',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) )
        = X13 )
      | ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

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

thf('22',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X32
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X29 @ X30 @ X31 @ X32 ) @ ( k6_mcart_1 @ X29 @ X30 @ X31 @ X32 ) @ ( k7_mcart_1 @ X29 @ X30 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ X29 @ X30 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('26',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_mcart_1 @ X19 @ X20 @ X21 )
      = ( k4_tarski @ ( k4_tarski @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('32',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r2_hidden @ X34 @ X33 )
      | ( ( sk_B_1 @ X33 )
       != ( k4_tarski @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_B_1 @ X3 )
       != ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ X0 )
       != sk_D_2 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B_1 @ X0 )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ( ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ sk_D_2 ) )
       != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['21','35'])).

thf('37',plain,
    ( ( ( ( sk_B_1 @ ( k1_tarski @ sk_D_2 ) )
       != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X15 @ X17 ) @ X18 )
        = ( k2_tarski @ X15 @ X17 ) )
      | ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('39',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('40',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ ( sk_B @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0 = X1 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('47',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('48',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('49',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ( ( sk_B @ X25 )
       != ( k3_mcart_1 @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_2 )
      | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_2 ) )
       != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_2 ) )
       != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( sk_D_2 != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_D_2 )
      = k1_xboole_0 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X13 @ ( k1_tarski @ X12 ) )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D_2 @ X0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_D_2 ) @ k1_xboole_0 )
       != ( k2_tarski @ X0 @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_2 )
         != ( k2_tarski @ X0 @ sk_D_2 ) )
        | ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( r2_hidden @ sk_D_2 @ k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['38','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_D_2 @ k1_xboole_0 )
        | ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_D_2 @ k1_xboole_0 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(condensation,[status(thm)],['60'])).

thf('62',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('67',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['72'])).

thf('74',plain,(
    sk_D_2
 != ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','73'])).

thf('75',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X15 @ X17 ) @ X18 )
        = ( k2_tarski @ X15 @ X17 ) )
      | ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('76',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['44'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('79',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('80',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('81',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ( ( sk_B @ X25 )
       != ( k3_mcart_1 @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_2 )
      | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_2 ) )
       != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_2 ) )
       != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( sk_D_2 != sk_D_2 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_D_2 )
        = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_D_2 )
      = k1_xboole_0 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X13 @ ( k1_tarski @ X12 ) )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D_2 @ X0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_D_2 ) @ k1_xboole_0 )
       != ( k2_tarski @ X0 @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['76','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_2 )
         != ( k2_tarski @ X0 @ sk_D_2 ) )
        | ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( r2_hidden @ sk_D_2 @ k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['75','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_D_2 @ k1_xboole_0 )
        | ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( r2_hidden @ sk_D_2 @ k1_xboole_0 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(condensation,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['72'])).

thf('95',plain,(
    sk_D_2
 != ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('97',plain,
    ( sk_D_2
    = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['74','95','96'])).

thf('98',plain,
    ( ( ( sk_B_1 @ ( k1_tarski @ sk_D_2 ) )
     != sk_D_2 )
    | ( ( k1_tarski @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['37','97'])).

thf('99',plain,
    ( ( sk_D_2 != sk_D_2 )
    | ( ( k1_tarski @ sk_D_2 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','98'])).

thf('100',plain,
    ( ( k1_tarski @ sk_D_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X13 @ ( k1_tarski @ X12 ) )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
       != X0 )
      | ~ ( r2_hidden @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_D_2 ) @ k1_xboole_0 )
     != ( k2_tarski @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ sk_D_2 )
       != ( k2_tarski @ X0 @ sk_D_2 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ sk_D_2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_2 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    r2_hidden @ sk_D_2 @ k1_xboole_0 ),
    inference(condensation,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['72'])).

thf('108',plain,(
    $false ),
    inference('sup-',[status(thm)],['106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sBaAmqG35l
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:53:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 445 iterations in 0.185s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.64  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.47/0.64  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.47/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.47/0.64  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.47/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.64  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.47/0.64  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.47/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.64  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.64  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.47/0.64  thf(t72_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.47/0.64       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.47/0.64  thf('0', plain,
% 0.47/0.64      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ (k2_tarski @ X15 @ X17) @ X18)
% 0.47/0.64            = (k2_tarski @ X15 @ X17))
% 0.47/0.64          | (r2_hidden @ X17 @ X18)
% 0.47/0.64          | (r2_hidden @ X15 @ X18))),
% 0.47/0.64      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.47/0.64  thf(d2_tarski, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.64         (((X7) != (X6))
% 0.47/0.64          | (r2_hidden @ X7 @ X8)
% 0.47/0.64          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d2_tarski])).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.47/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.64  thf(t9_mcart_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ![B:$i]:
% 0.47/0.64            ( ~( ( r2_hidden @ B @ A ) & 
% 0.47/0.64                 ( ![C:$i,D:$i]:
% 0.47/0.64                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.47/0.64                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X33 : $i]:
% 0.47/0.64         (((X33) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X33) @ X33))),
% 0.47/0.64      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.47/0.64  thf(t65_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.47/0.64       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X13 : $i, X14 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ X13 @ (k1_tarski @ X14)) = (X13))
% 0.47/0.64          | (r2_hidden @ X14 @ X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X15 @ X16)
% 0.47/0.64          | ((k4_xboole_0 @ (k2_tarski @ X15 @ X17) @ X16)
% 0.47/0.64              != (k2_tarski @ X15 @ X17)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 0.47/0.64          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.47/0.64          | ~ (r2_hidden @ X1 @ (k1_tarski @ X2)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X1 @ (k1_tarski @ X2))
% 0.47/0.64          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['6'])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ X0 @ (k2_tarski @ (sk_B_1 @ (k1_tarski @ X0)) @ X1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['3', '7'])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X10 @ X8)
% 0.47/0.64          | ((X10) = (X9))
% 0.47/0.64          | ((X10) = (X6))
% 0.47/0.64          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d2_tarski])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X6 : $i, X9 : $i, X10 : $i]:
% 0.47/0.64         (((X10) = (X6))
% 0.47/0.64          | ((X10) = (X9))
% 0.47/0.64          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_tarski @ X1) = (k1_xboole_0))
% 0.47/0.64          | ((X1) = (sk_B_1 @ (k1_tarski @ X1)))
% 0.47/0.64          | ((X1) = (X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['8', '10'])).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | ((X0) = (sk_B_1 @ (k1_tarski @ X0))))),
% 0.47/0.64      inference('condensation', [status(thm)], ['11'])).
% 0.47/0.64  thf(t29_mcart_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ![B:$i]:
% 0.47/0.64            ( ~( ( r2_hidden @ B @ A ) & 
% 0.47/0.64                 ( ![C:$i,D:$i,E:$i]:
% 0.47/0.64                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.47/0.64                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      (![X25 : $i]:
% 0.47/0.64         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.47/0.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X25 : $i]:
% 0.47/0.64         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.47/0.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (![X13 : $i, X14 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ X13 @ (k1_tarski @ X14)) = (X13))
% 0.47/0.64          | (r2_hidden @ X14 @ X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.47/0.64  thf(d5_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.64           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X4 @ X3)
% 0.47/0.64          | ~ (r2_hidden @ X4 @ X2)
% 0.47/0.64          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X4 @ X2)
% 0.47/0.64          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X2 @ X0)
% 0.47/0.64          | (r2_hidden @ X1 @ X0)
% 0.47/0.64          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['15', '17'])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ X0 @ X1)
% 0.47/0.64          | ~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ X1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '18'])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['13', '19'])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['20'])).
% 0.47/0.64  thf(t51_mcart_1, conjecture,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ~( ![D:$i]:
% 0.47/0.64               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.47/0.64                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.47/0.64                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.47/0.64                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.64        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64             ( ~( ![D:$i]:
% 0.47/0.64                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.47/0.64                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.47/0.64                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.47/0.64                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))
% 0.47/0.64        | ((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))
% 0.47/0.64        | ((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))
% 0.47/0.64         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('split', [status(esa)], ['22'])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t48_mcart_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ~( ![D:$i]:
% 0.47/0.64               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.47/0.64                 ( ( D ) =
% 0.47/0.64                   ( k3_mcart_1 @
% 0.47/0.64                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.47/0.64                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.47/0.64                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.47/0.64         (((X29) = (k1_xboole_0))
% 0.47/0.64          | ((X30) = (k1_xboole_0))
% 0.47/0.64          | ((X32)
% 0.47/0.64              = (k3_mcart_1 @ (k5_mcart_1 @ X29 @ X30 @ X31 @ X32) @ 
% 0.47/0.64                 (k6_mcart_1 @ X29 @ X30 @ X31 @ X32) @ 
% 0.47/0.64                 (k7_mcart_1 @ X29 @ X30 @ X31 @ X32)))
% 0.47/0.64          | ~ (m1_subset_1 @ X32 @ (k3_zfmisc_1 @ X29 @ X30 @ X31))
% 0.47/0.64          | ((X31) = (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))
% 0.47/0.64        | ((sk_D_2)
% 0.47/0.64            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ 
% 0.47/0.64               (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ 
% 0.47/0.64               (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))
% 0.47/0.64        | ((sk_B_2) = (k1_xboole_0))
% 0.47/0.64        | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.64  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('28', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (((sk_D_2)
% 0.47/0.64         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ 
% 0.47/0.64            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ 
% 0.47/0.64            (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.47/0.64  thf(d3_mcart_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.64         ((k3_mcart_1 @ X19 @ X20 @ X21)
% 0.47/0.64           = (k4_tarski @ (k4_tarski @ X19 @ X20) @ X21))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.64         (((X33) = (k1_xboole_0))
% 0.47/0.64          | ~ (r2_hidden @ X34 @ X33)
% 0.47/0.64          | ((sk_B_1 @ X33) != (k4_tarski @ X35 @ X34)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         (((sk_B_1 @ X3) != (k3_mcart_1 @ X2 @ X1 @ X0))
% 0.47/0.64          | ~ (r2_hidden @ X0 @ X3)
% 0.47/0.64          | ((X3) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.64  thf('34', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((sk_B_1 @ X0) != (sk_D_2))
% 0.47/0.64          | ((X0) = (k1_xboole_0))
% 0.47/0.64          | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['30', '33'])).
% 0.47/0.64  thf('35', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (r2_hidden @ sk_D_2 @ X0)
% 0.47/0.64           | ((X0) = (k1_xboole_0))
% 0.47/0.64           | ((sk_B_1 @ X0) != (sk_D_2))))
% 0.47/0.64         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['23', '34'])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      (((((k1_tarski @ sk_D_2) = (k1_xboole_0))
% 0.47/0.64         | ((sk_B_1 @ (k1_tarski @ sk_D_2)) != (sk_D_2))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.47/0.64         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['21', '35'])).
% 0.47/0.64  thf('37', plain,
% 0.47/0.64      (((((sk_B_1 @ (k1_tarski @ sk_D_2)) != (sk_D_2))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.47/0.64         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['36'])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ (k2_tarski @ X15 @ X17) @ X18)
% 0.47/0.64            = (k2_tarski @ X15 @ X17))
% 0.47/0.64          | (r2_hidden @ X17 @ X18)
% 0.47/0.64          | (r2_hidden @ X15 @ X18))),
% 0.47/0.64      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.47/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.47/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ X0 @ X1)
% 0.47/0.64          | ~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ X1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '18'])).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r2_hidden @ X0 @ (k2_tarski @ X1 @ (sk_B @ (k1_tarski @ X0))))
% 0.47/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X6 : $i, X9 : $i, X10 : $i]:
% 0.47/0.64         (((X10) = (X6))
% 0.47/0.64          | ((X10) = (X9))
% 0.47/0.64          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | ((X0) = (X1))
% 0.47/0.64          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.47/0.64      inference('condensation', [status(thm)], ['44'])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['20'])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('split', [status(esa)], ['22'])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (((sk_D_2)
% 0.47/0.64         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ 
% 0.47/0.64            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ 
% 0.47/0.64            (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.64         (((X25) = (k1_xboole_0))
% 0.47/0.64          | ~ (r2_hidden @ X26 @ X25)
% 0.47/0.64          | ((sk_B @ X25) != (k3_mcart_1 @ X27 @ X26 @ X28)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((sk_B @ X0) != (sk_D_2))
% 0.47/0.64          | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ X0)
% 0.47/0.64          | ((X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (r2_hidden @ sk_D_2 @ X0)
% 0.47/0.64           | ((X0) = (k1_xboole_0))
% 0.47/0.64           | ((sk_B @ X0) != (sk_D_2))))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['47', '50'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      (((((k1_tarski @ sk_D_2) = (k1_xboole_0))
% 0.47/0.64         | ((sk_B @ (k1_tarski @ sk_D_2)) != (sk_D_2))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['46', '51'])).
% 0.47/0.64  thf('53', plain,
% 0.47/0.64      (((((sk_B @ (k1_tarski @ sk_D_2)) != (sk_D_2))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['52'])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      (((((sk_D_2) != (sk_D_2))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['45', '53'])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      ((((k1_tarski @ sk_D_2) = (k1_xboole_0)))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['54'])).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X12 : $i, X13 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X12 @ X13)
% 0.47/0.64          | ((k4_xboole_0 @ X13 @ (k1_tarski @ X12)) != (X13)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.47/0.64           | ~ (r2_hidden @ sk_D_2 @ X0)))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_D_2) @ k1_xboole_0)
% 0.47/0.64            != (k2_tarski @ X0 @ sk_D_2)))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['39', '57'])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (((k2_tarski @ X0 @ sk_D_2) != (k2_tarski @ X0 @ sk_D_2))
% 0.47/0.64           | (r2_hidden @ X0 @ k1_xboole_0)
% 0.47/0.64           | (r2_hidden @ sk_D_2 @ k1_xboole_0)))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['38', '58'])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          ((r2_hidden @ sk_D_2 @ k1_xboole_0) | (r2_hidden @ X0 @ k1_xboole_0)))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['59'])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      (((r2_hidden @ sk_D_2 @ k1_xboole_0))
% 0.47/0.64         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('condensation', [status(thm)], ['60'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (![X25 : $i]:
% 0.47/0.64         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.47/0.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X4 @ X3)
% 0.47/0.64          | (r2_hidden @ X4 @ X1)
% 0.47/0.64          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.64         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['63'])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['62', '64'])).
% 0.47/0.64  thf('66', plain,
% 0.47/0.64      (![X25 : $i]:
% 0.47/0.64         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.47/0.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.47/0.64  thf('67', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X4 @ X2)
% 0.47/0.64          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.64  thf('68', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.47/0.64          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['66', '67'])).
% 0.47/0.64  thf('69', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.47/0.64          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['65', '68'])).
% 0.47/0.64  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['69'])).
% 0.47/0.64  thf('71', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X4 @ X2)
% 0.47/0.64          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.64  thf('72', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.47/0.64  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.47/0.64      inference('condensation', [status(thm)], ['72'])).
% 0.47/0.64  thf('74', plain,
% 0.47/0.64      (~ (((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['61', '73'])).
% 0.47/0.64  thf('75', plain,
% 0.47/0.64      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ (k2_tarski @ X15 @ X17) @ X18)
% 0.47/0.64            = (k2_tarski @ X15 @ X17))
% 0.47/0.64          | (r2_hidden @ X17 @ X18)
% 0.47/0.64          | (r2_hidden @ X15 @ X18))),
% 0.47/0.64      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.47/0.64  thf('76', plain,
% 0.47/0.64      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.47/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.64  thf('77', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.47/0.64      inference('condensation', [status(thm)], ['44'])).
% 0.47/0.64  thf('78', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.47/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['20'])).
% 0.47/0.64  thf('79', plain,
% 0.47/0.64      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('split', [status(esa)], ['22'])).
% 0.47/0.64  thf('80', plain,
% 0.47/0.64      (((sk_D_2)
% 0.47/0.64         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ 
% 0.47/0.64            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ 
% 0.47/0.64            (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.47/0.64  thf('81', plain,
% 0.47/0.64      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.64         (((X25) = (k1_xboole_0))
% 0.47/0.64          | ~ (r2_hidden @ X27 @ X25)
% 0.47/0.64          | ((sk_B @ X25) != (k3_mcart_1 @ X27 @ X26 @ X28)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.47/0.64  thf('82', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((sk_B @ X0) != (sk_D_2))
% 0.47/0.64          | ~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2) @ X0)
% 0.47/0.64          | ((X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['80', '81'])).
% 0.47/0.64  thf('83', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (r2_hidden @ sk_D_2 @ X0)
% 0.47/0.64           | ((X0) = (k1_xboole_0))
% 0.47/0.64           | ((sk_B @ X0) != (sk_D_2))))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['79', '82'])).
% 0.47/0.64  thf('84', plain,
% 0.47/0.64      (((((k1_tarski @ sk_D_2) = (k1_xboole_0))
% 0.47/0.64         | ((sk_B @ (k1_tarski @ sk_D_2)) != (sk_D_2))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['78', '83'])).
% 0.47/0.64  thf('85', plain,
% 0.47/0.64      (((((sk_B @ (k1_tarski @ sk_D_2)) != (sk_D_2))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['84'])).
% 0.47/0.64  thf('86', plain,
% 0.47/0.64      (((((sk_D_2) != (sk_D_2))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))
% 0.47/0.64         | ((k1_tarski @ sk_D_2) = (k1_xboole_0))))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['77', '85'])).
% 0.47/0.64  thf('87', plain,
% 0.47/0.64      ((((k1_tarski @ sk_D_2) = (k1_xboole_0)))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['86'])).
% 0.47/0.64  thf('88', plain,
% 0.47/0.64      (![X12 : $i, X13 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X12 @ X13)
% 0.47/0.64          | ((k4_xboole_0 @ X13 @ (k1_tarski @ X12)) != (X13)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.47/0.64  thf('89', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.47/0.64           | ~ (r2_hidden @ sk_D_2 @ X0)))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.64  thf('90', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_D_2) @ k1_xboole_0)
% 0.47/0.64            != (k2_tarski @ X0 @ sk_D_2)))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['76', '89'])).
% 0.47/0.64  thf('91', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (((k2_tarski @ X0 @ sk_D_2) != (k2_tarski @ X0 @ sk_D_2))
% 0.47/0.64           | (r2_hidden @ X0 @ k1_xboole_0)
% 0.47/0.64           | (r2_hidden @ sk_D_2 @ k1_xboole_0)))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['75', '90'])).
% 0.47/0.64  thf('92', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          ((r2_hidden @ sk_D_2 @ k1_xboole_0) | (r2_hidden @ X0 @ k1_xboole_0)))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['91'])).
% 0.47/0.64  thf('93', plain,
% 0.47/0.64      (((r2_hidden @ sk_D_2 @ k1_xboole_0))
% 0.47/0.64         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))))),
% 0.47/0.64      inference('condensation', [status(thm)], ['92'])).
% 0.47/0.64  thf('94', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.47/0.64      inference('condensation', [status(thm)], ['72'])).
% 0.47/0.64  thf('95', plain,
% 0.47/0.64      (~ (((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['93', '94'])).
% 0.47/0.64  thf('96', plain,
% 0.47/0.64      ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))) | 
% 0.47/0.64       (((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2))) | 
% 0.47/0.64       (((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))),
% 0.47/0.64      inference('split', [status(esa)], ['22'])).
% 0.47/0.64  thf('97', plain,
% 0.47/0.64      ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_2)))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['74', '95', '96'])).
% 0.47/0.64  thf('98', plain,
% 0.47/0.64      ((((sk_B_1 @ (k1_tarski @ sk_D_2)) != (sk_D_2))
% 0.47/0.64        | ((k1_tarski @ sk_D_2) = (k1_xboole_0)))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['37', '97'])).
% 0.47/0.64  thf('99', plain,
% 0.47/0.64      ((((sk_D_2) != (sk_D_2))
% 0.47/0.64        | ((k1_tarski @ sk_D_2) = (k1_xboole_0))
% 0.47/0.64        | ((k1_tarski @ sk_D_2) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['12', '98'])).
% 0.47/0.64  thf('100', plain, (((k1_tarski @ sk_D_2) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['99'])).
% 0.47/0.64  thf('101', plain,
% 0.47/0.64      (![X12 : $i, X13 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X12 @ X13)
% 0.47/0.64          | ((k4_xboole_0 @ X13 @ (k1_tarski @ X12)) != (X13)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.47/0.64  thf('102', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.47/0.64          | ~ (r2_hidden @ sk_D_2 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['100', '101'])).
% 0.47/0.64  thf('103', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_D_2) @ k1_xboole_0)
% 0.47/0.64           != (k2_tarski @ X0 @ sk_D_2))),
% 0.47/0.64      inference('sup-', [status(thm)], ['2', '102'])).
% 0.47/0.64  thf('104', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k2_tarski @ X0 @ sk_D_2) != (k2_tarski @ X0 @ sk_D_2))
% 0.47/0.64          | (r2_hidden @ X0 @ k1_xboole_0)
% 0.47/0.64          | (r2_hidden @ sk_D_2 @ k1_xboole_0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '103'])).
% 0.47/0.64  thf('105', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ sk_D_2 @ k1_xboole_0) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['104'])).
% 0.47/0.64  thf('106', plain, ((r2_hidden @ sk_D_2 @ k1_xboole_0)),
% 0.47/0.64      inference('condensation', [status(thm)], ['105'])).
% 0.47/0.64  thf('107', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.47/0.64      inference('condensation', [status(thm)], ['72'])).
% 0.47/0.64  thf('108', plain, ($false), inference('sup-', [status(thm)], ['106', '107'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
