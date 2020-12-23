%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xo0jXOjeC7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 289 expanded)
%              Number of leaves         :   28 (  95 expanded)
%              Depth                    :   23
%              Number of atoms          : 1046 (5277 expanded)
%              Number of equality atoms :  160 ( 860 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X26
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X23 @ X24 @ X25 @ X26 ) @ ( k6_mcart_1 @ X23 @ X24 @ X25 @ X26 ) @ ( k7_mcart_1 @ X23 @ X24 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ X23 @ X24 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('4',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X27 @ X28 @ X30 @ X29 )
        = ( k2_mcart_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X27 @ X28 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('7',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X27 @ X28 @ X30 @ X29 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X27 @ X28 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('19',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10'])).

thf('28',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['25'])).

thf('29',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('31',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_mcart_1 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k2_mcart_1 @ X16 ) )
      | ( X16
       != ( k4_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_tarski @ X17 @ X18 )
     != ( k2_mcart_1 @ ( k4_tarski @ X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('35',plain,(
    ! [X31: $i,X33: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X31 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_tarski @ X17 @ X18 )
     != X18 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('40',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['25'])).

thf('41',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

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

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ( ( sk_B @ X19 )
       != ( k3_mcart_1 @ X21 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D )
      | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D ) )
       != sk_D )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('48',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,
    ( ( ( sk_D != sk_D )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','56'])).

thf('58',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('60',plain,
    ( ( r2_hidden @ sk_D @ k1_xboole_0 )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('62',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['25'])).

thf('64',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['38','62','63'])).

thf('65',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['26','64'])).

thf('66',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('67',plain,
    ( sk_D
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X27 @ X28 @ X30 @ X29 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X27 @ X28 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('70',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( sk_D
    = ( k3_mcart_1 @ sk_D @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','67','74'])).

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ( ( sk_B @ X19 )
       != ( k3_mcart_1 @ X21 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D )
      | ~ ( r2_hidden @ sk_D @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_D ) )
     != sk_D ) ),
    inference('sup-',[status(thm)],['1','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('80',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
    | ( sk_D != sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_tarski @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('83',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('85',plain,(
    $false ),
    inference('sup-',[status(thm)],['83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xo0jXOjeC7
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 118 iterations in 0.048s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(d1_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.51  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['0'])).
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
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
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
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.51         (((X23) = (k1_xboole_0))
% 0.21/0.51          | ((X24) = (k1_xboole_0))
% 0.21/0.51          | ((X26)
% 0.21/0.51              = (k3_mcart_1 @ (k5_mcart_1 @ X23 @ X24 @ X25 @ X26) @ 
% 0.21/0.51                 (k6_mcart_1 @ X23 @ X24 @ X25 @ X26) @ 
% 0.21/0.51                 (k7_mcart_1 @ X23 @ X24 @ X25 @ X26)))
% 0.21/0.51          | ~ (m1_subset_1 @ X26 @ (k3_zfmisc_1 @ X23 @ X24 @ X25))
% 0.21/0.51          | ((X25) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_D)
% 0.21/0.51            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.51               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.51               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.21/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t50_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ~( ![D:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.51                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.51                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.51                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.51                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.51         (((X27) = (k1_xboole_0))
% 0.21/0.51          | ((X28) = (k1_xboole_0))
% 0.21/0.51          | ((k7_mcart_1 @ X27 @ X28 @ X30 @ X29) = (k2_mcart_1 @ X29))
% 0.21/0.51          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X27 @ X28 @ X30))
% 0.21/0.51          | ((X30) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.51        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.21/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_D)
% 0.21/0.51            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.51               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.51               (k2_mcart_1 @ sk_D)))
% 0.21/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '11'])).
% 0.21/0.51  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.51         (((X27) = (k1_xboole_0))
% 0.21/0.51          | ((X28) = (k1_xboole_0))
% 0.21/0.51          | ((k5_mcart_1 @ X27 @ X28 @ X30 @ X29)
% 0.21/0.51              = (k1_mcart_1 @ (k1_mcart_1 @ X29)))
% 0.21/0.51          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X27 @ X28 @ X30))
% 0.21/0.51          | ((X30) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.51        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.21/0.51            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.21/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.21/0.51        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.21/0.51        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.21/0.51         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.21/0.51         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['25'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((((sk_D) = (k2_mcart_1 @ sk_D)))
% 0.21/0.51         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((((sk_D)
% 0.21/0.51          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.51             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_D)))
% 0.21/0.51         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf(d3_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((k3_mcart_1 @ X10 @ X11 @ X12)
% 0.21/0.51           = (k4_tarski @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.51  thf(t20_mcart_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.51       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (((X16) != (k2_mcart_1 @ X16)) | ((X16) != (k4_tarski @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         ((k4_tarski @ X17 @ X18) != (k2_mcart_1 @ (k4_tarski @ X17 @ X18)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.51  thf(t7_mcart_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.51       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X31 : $i, X33 : $i]: ((k2_mcart_1 @ (k4_tarski @ X31 @ X33)) = (X33))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.51  thf('36', plain, (![X17 : $i, X18 : $i]: ((k4_tarski @ X17 @ X18) != (X18))),
% 0.21/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['31', '37'])).
% 0.21/0.51  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.21/0.51         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['25'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.51            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.51  thf(t29_mcart_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.51                 ( ![C:$i,D:$i,E:$i]:
% 0.21/0.51                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.51                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (((X19) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X20 @ X19)
% 0.21/0.51          | ((sk_B @ X19) != (k3_mcart_1 @ X21 @ X20 @ X22)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_B @ X0) != (sk_D))
% 0.21/0.51          | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ X0)
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (r2_hidden @ sk_D @ X0)
% 0.21/0.51           | ((X0) = (k1_xboole_0))
% 0.21/0.51           | ((sk_B @ X0) != (sk_D))))
% 0.21/0.51         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((((sk_B @ (k1_tarski @ sk_D)) != (sk_D))
% 0.21/0.51         | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.21/0.51         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X19 : $i]:
% 0.21/0.51         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X0 : $i, X3 : $i]:
% 0.21/0.51         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.51          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '48'])).
% 0.21/0.51  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ k1_xboole_0) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf(t113_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.51  thf(t152_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.51  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((((sk_D) != (sk_D)) | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.21/0.51         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.51  thf('59', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (((r2_hidden @ sk_D @ k1_xboole_0))
% 0.21/0.51         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('61', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (~ (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.21/0.51       (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.21/0.51       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['25'])).
% 0.21/0.51  thf('64', plain, ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['38', '62', '63'])).
% 0.21/0.51  thf('65', plain, (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['26', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.21/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.21/0.51  thf('67', plain, (((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.51         (((X27) = (k1_xboole_0))
% 0.21/0.51          | ((X28) = (k1_xboole_0))
% 0.21/0.51          | ((k6_mcart_1 @ X27 @ X28 @ X30 @ X29)
% 0.21/0.51              = (k2_mcart_1 @ (k1_mcart_1 @ X29)))
% 0.21/0.51          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X27 @ X28 @ X30))
% 0.21/0.51          | ((X30) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.51        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.21/0.51            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.21/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('72', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('73', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)
% 0.21/0.51         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['70', '71', '72', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (((sk_D)
% 0.21/0.51         = (k3_mcart_1 @ sk_D @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.21/0.51            (k2_mcart_1 @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '67', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (((X19) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X21 @ X19)
% 0.21/0.51          | ((sk_B @ X19) != (k3_mcart_1 @ X21 @ X20 @ X22)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_B @ X0) != (sk_D))
% 0.21/0.51          | ~ (r2_hidden @ sk_D @ X0)
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      ((((k1_tarski @ sk_D) = (k1_xboole_0))
% 0.21/0.51        | ((sk_B @ (k1_tarski @ sk_D)) != (sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '77'])).
% 0.21/0.51  thf('79', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '55'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      ((((k1_tarski @ sk_D) = (k1_xboole_0)) | ((sk_D) != (sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.51  thf('81', plain, (((k1_tarski @ sk_D) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['80'])).
% 0.21/0.51  thf('82', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.51  thf('83', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('84', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('85', plain, ($false), inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
