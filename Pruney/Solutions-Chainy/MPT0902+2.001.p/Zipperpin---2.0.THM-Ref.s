%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dqw35JbJYu

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 389 expanded)
%              Number of leaves         :   36 ( 131 expanded)
%              Depth                    :   22
%              Number of atoms          : 1493 (9718 expanded)
%              Number of equality atoms :  210 (1498 expanded)
%              Maximal formula depth    :   24 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(t62_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( E
                 != ( k8_mcart_1 @ A @ B @ C @ D @ E ) )
                & ( E
                 != ( k9_mcart_1 @ A @ B @ C @ D @ E ) )
                & ( E
                 != ( k10_mcart_1 @ A @ B @ C @ D @ E ) )
                & ( E
                 != ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ~ ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
               => ( ( E
                   != ( k8_mcart_1 @ A @ B @ C @ D @ E ) )
                  & ( E
                   != ( k9_mcart_1 @ A @ B @ C @ D @ E ) )
                  & ( E
                   != ( k10_mcart_1 @ A @ B @ C @ D @ E ) )
                  & ( E
                   != ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k4_zfmisc_1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf(t26_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( X20
       != ( k2_mcart_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k2_zfmisc_1 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X4
       != ( k2_mcart_1 @ X4 ) )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_E
     != ( k2_mcart_1 @ sk_E ) )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_mcart_1,axiom,(
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

thf('6',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('7',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10','11'])).

thf('13',plain,
    ( ( sk_E
      = ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
    | ( sk_E
      = ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
    | ( sk_E
      = ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
    | ( sk_E
      = ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_E
      = ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
   <= ( sk_E
      = ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_E
      = ( k2_mcart_1 @ sk_E ) )
   <= ( sk_E
      = ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( sk_E
      = ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
   <= ( sk_E
      = ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D ) ),
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

thf('18',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X48
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48 ) @ ( k9_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48 ) @ ( k10_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48 ) @ ( k11_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k4_zfmisc_1 @ X44 @ X45 @ X46 @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('19',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( X49 = k1_xboole_0 )
      | ( X50 = k1_xboole_0 )
      | ( X51 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53 ) )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('22',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25','26'])).

thf('28',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['7','8','9','10','11'])).

thf('29',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','27','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32','33'])).

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

thf('35',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('36',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( X5 = X2 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5 = X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ( ( sk_B_1 @ X30 )
       != ( k4_mcart_1 @ X32 @ X31 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0
       != ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k1_tarski @ ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k1_tarski @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k1_tarski @ sk_E ) )
   <= ( sk_E
      = ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['16','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X3 != X2 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('51',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    sk_E
 != ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['49','51'])).

thf('53',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25','26'])).

thf('54',plain,
    ( ( sk_E
      = ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
   <= ( sk_E
      = ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['13'])).

thf('55',plain,
    ( ( sk_E
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
   <= ( sk_E
      = ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32','33'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('57',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('59',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_mcart_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k3_mcart_1 @ X26 @ X27 @ X28 ) @ X29 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_mcart_1 @ X16 @ X17 @ X18 )
      = ( k4_tarski @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 )
      = ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

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

thf('64',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('65',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5 = X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k3_mcart_1 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('73',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k1_tarski @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k1_tarski @ sk_E ) )
   <= ( sk_E
      = ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['55','75'])).

thf('77',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('78',plain,(
    sk_E
 != ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_E
      = ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
   <= ( sk_E
      = ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['13'])).

thf('80',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32','33'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

thf('82',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ( ( sk_B_1 @ X30 )
       != ( k4_mcart_1 @ X32 @ X31 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0
       != ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k1_tarski @ ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('86',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( r2_hidden @ X4 @ ( k1_tarski @ ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) @ ( k1_tarski @ sk_E ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k1_tarski @ sk_E ) )
   <= ( sk_E
      = ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('90',plain,(
    sk_E
 != ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_E
      = ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
    | ( sk_E
      = ( k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
    | ( sk_E
      = ( k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) )
    | ( sk_E
      = ( k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['13'])).

thf('92',plain,
    ( sk_E
    = ( k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['52','78','90','91'])).

thf('93',plain,
    ( sk_E
    = ( k2_mcart_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['15','92'])).

thf('94',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_E != sk_E )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','93'])).

thf('95',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('98',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X10 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('99',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X10 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('104',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['105','106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dqw35JbJYu
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 191 iterations in 0.078s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.53  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.53  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(t62_mcart_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ~( ![E:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.53                 ( ( ( E ) != ( k8_mcart_1 @ A @ B @ C @ D @ E ) ) & 
% 0.20/0.53                   ( ( E ) != ( k9_mcart_1 @ A @ B @ C @ D @ E ) ) & 
% 0.20/0.53                   ( ( E ) != ( k10_mcart_1 @ A @ B @ C @ D @ E ) ) & 
% 0.20/0.53                   ( ( E ) != ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53             ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53             ( ~( ![E:$i]:
% 0.20/0.53                  ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.53                    ( ( ( E ) != ( k8_mcart_1 @ A @ B @ C @ D @ E ) ) & 
% 0.20/0.53                      ( ( E ) != ( k9_mcart_1 @ A @ B @ C @ D @ E ) ) & 
% 0.20/0.53                      ( ( E ) != ( k10_mcart_1 @ A @ B @ C @ D @ E ) ) & 
% 0.20/0.53                      ( ( E ) != ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t62_mcart_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t53_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.20/0.53       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.53         ((k4_zfmisc_1 @ X35 @ X36 @ X37 @ X38)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36) @ X37) @ 
% 0.20/0.53              X38))),
% 0.20/0.53      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.53  thf(t26_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ~( ![C:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.53                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.53                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (((X19) = (k1_xboole_0))
% 0.20/0.53          | ((X20) != (k2_mcart_1 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (k2_zfmisc_1 @ X19 @ X21))
% 0.20/0.53          | ((X21) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X4) != (k2_mcart_1 @ X4))
% 0.20/0.53          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((((k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2) @ sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_E) != (k2_mcart_1 @ sk_E))
% 0.20/0.53        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t61_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ~( ![E:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.53                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.53                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.53                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.53                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.20/0.53                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (((X49) = (k1_xboole_0))
% 0.20/0.53          | ((X50) = (k1_xboole_0))
% 0.20/0.53          | ((X51) = (k1_xboole_0))
% 0.20/0.53          | ((k11_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52) = (k2_mcart_1 @ X52))
% 0.20/0.53          | ~ (m1_subset_1 @ X52 @ (k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53))
% 0.20/0.53          | ((X53) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((((sk_D) = (k1_xboole_0))
% 0.20/0.53        | ((k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)
% 0.20/0.53            = (k2_mcart_1 @ sk_E))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B_2) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (((k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)
% 0.20/0.53         = (k2_mcart_1 @ sk_E))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((((sk_E) = (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))
% 0.20/0.53        | ((sk_E) = (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))
% 0.20/0.53        | ((sk_E) = (k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))
% 0.20/0.53        | ((sk_E) = (k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((((sk_E) = (k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))
% 0.20/0.53         <= ((((sk_E) = (k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('split', [status(esa)], ['13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((((sk_E) = (k2_mcart_1 @ sk_E)))
% 0.20/0.53         <= ((((sk_E) = (k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['12', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((((sk_E) = (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))
% 0.20/0.53         <= ((((sk_E) = (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('split', [status(esa)], ['13'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t60_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ~( ![E:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.53                 ( ( E ) =
% 0.20/0.53                   ( k4_mcart_1 @
% 0.20/0.53                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.53                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.53                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.53                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.20/0.53         (((X44) = (k1_xboole_0))
% 0.20/0.53          | ((X45) = (k1_xboole_0))
% 0.20/0.53          | ((X46) = (k1_xboole_0))
% 0.20/0.53          | ((X48)
% 0.20/0.53              = (k4_mcart_1 @ (k8_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48) @ 
% 0.20/0.53                 (k9_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48) @ 
% 0.20/0.53                 (k10_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48) @ 
% 0.20/0.53                 (k11_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48)))
% 0.20/0.53          | ~ (m1_subset_1 @ X48 @ (k4_zfmisc_1 @ X44 @ X45 @ X46 @ X47))
% 0.20/0.53          | ((X47) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t60_mcart_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((sk_D) = (k1_xboole_0))
% 0.20/0.53        | ((sk_E)
% 0.20/0.53            = (k4_mcart_1 @ 
% 0.20/0.53               (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53               (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53               (k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53               (k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B_2) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.53         (((X49) = (k1_xboole_0))
% 0.20/0.53          | ((X50) = (k1_xboole_0))
% 0.20/0.53          | ((X51) = (k1_xboole_0))
% 0.20/0.53          | ((k10_mcart_1 @ X49 @ X50 @ X51 @ X53 @ X52)
% 0.20/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X52)))
% 0.20/0.53          | ~ (m1_subset_1 @ X52 @ (k4_zfmisc_1 @ X49 @ X50 @ X51 @ X53))
% 0.20/0.53          | ((X53) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((sk_D) = (k1_xboole_0))
% 0.20/0.53        | ((k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)
% 0.20/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B_2) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (((k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)
% 0.20/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)],
% 0.20/0.53                ['22', '23', '24', '25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)
% 0.20/0.53         = (k2_mcart_1 @ sk_E))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((sk_D) = (k1_xboole_0))
% 0.20/0.53        | ((sk_E)
% 0.20/0.53            = (k4_mcart_1 @ 
% 0.20/0.53               (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53               (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B_2) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '27', '28'])).
% 0.20/0.53  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (((sk_E)
% 0.20/0.53         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53            (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)],
% 0.20/0.53                ['29', '30', '31', '32', '33'])).
% 0.20/0.53  thf(t34_mcart_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.53                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.53                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X30 : $i]:
% 0.20/0.53         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X30) @ X30))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.20/0.53  thf(d1_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X5 @ X4) | ((X5) = (X2)) | ((X4) != (k1_tarski @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X2 : $i, X5 : $i]:
% 0.20/0.53         (((X5) = (X2)) | ~ (r2_hidden @ X5 @ (k1_tarski @ X2)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.53          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.53  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.53  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.53  thf(t49_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_tarski @ X14) @ X15) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.53  thf('41', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain, (![X0 : $i]: ((sk_B_1 @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.53         (((X30) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X31 @ X30)
% 0.20/0.53          | ((sk_B_1 @ X30) != (k4_mcart_1 @ X32 @ X31 @ X33 @ X34)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (((X0) != (k4_mcart_1 @ X4 @ X3 @ X2 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ (k1_tarski @ X0))
% 0.20/0.53          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (((k1_tarski @ (k4_mcart_1 @ X4 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ (k1_tarski @ (k4_mcart_1 @ X4 @ X3 @ X2 @ X1))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.53  thf('46', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ~ (r2_hidden @ X3 @ (k1_tarski @ (k4_mcart_1 @ X4 @ X3 @ X2 @ X1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53          (k1_tarski @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_E @ (k1_tarski @ sk_E)))
% 0.20/0.53         <= ((((sk_E) = (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (((X3) != (X2)) | (r2_hidden @ X3 @ X4) | ((X4) != (k1_tarski @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('51', plain, (![X2 : $i]: (r2_hidden @ X2 @ (k1_tarski @ X2))),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (~ (((sk_E) = (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))),
% 0.20/0.53      inference('demod', [status(thm)], ['49', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (((k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)
% 0.20/0.53         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)],
% 0.20/0.53                ['22', '23', '24', '25', '26'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((((sk_E) = (k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))
% 0.20/0.53         <= ((((sk_E) = (k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('split', [status(esa)], ['13'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      ((((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.20/0.53         <= ((((sk_E) = (k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (((sk_E)
% 0.20/0.53         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53            (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)],
% 0.20/0.53                ['29', '30', '31', '32', '33'])).
% 0.20/0.53  thf(t31_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.53       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.53         ((k4_mcart_1 @ X26 @ X27 @ X28 @ X29)
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28) @ X29))),
% 0.20/0.53      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.20/0.53  thf(d3_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.53         ((k4_mcart_1 @ X26 @ X27 @ X28 @ X29)
% 0.20/0.53           = (k4_tarski @ (k3_mcart_1 @ X26 @ X27 @ X28) @ X29))),
% 0.20/0.53      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ X16 @ X17 @ X18)
% 0.20/0.53           = (k4_tarski @ (k4_tarski @ X16 @ X17) @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.20/0.53           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.53      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k3_mcart_1 @ (k4_tarski @ X3 @ X2) @ X1 @ X0)
% 0.20/0.53           = (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['59', '62'])).
% 0.20/0.53  thf(t29_mcart_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.53                 ( ![C:$i,D:$i,E:$i]:
% 0.20/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.53                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (![X22 : $i]:
% 0.20/0.53         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X2 : $i, X5 : $i]:
% 0.20/0.53         (((X5) = (X2)) | ~ (r2_hidden @ X5 @ (k1_tarski @ X2)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.53          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('68', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         (((X22) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X23 @ X22)
% 0.20/0.53          | ((sk_B @ X22) != (k3_mcart_1 @ X24 @ X23 @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.20/0.53          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.53  thf('72', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ~ (r2_hidden @ X1 @ (k1_tarski @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['63', '73'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k1_tarski @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['56', '74'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_E @ (k1_tarski @ sk_E)))
% 0.20/0.53         <= ((((sk_E) = (k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '75'])).
% 0.20/0.53  thf('77', plain, (![X2 : $i]: (r2_hidden @ X2 @ (k1_tarski @ X2))),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (~ (((sk_E) = (k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))),
% 0.20/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      ((((sk_E) = (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))
% 0.20/0.53         <= ((((sk_E) = (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('split', [status(esa)], ['13'])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (((sk_E)
% 0.20/0.53         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53            (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)],
% 0.20/0.53                ['29', '30', '31', '32', '33'])).
% 0.20/0.53  thf('81', plain, (![X0 : $i]: ((sk_B_1 @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.53         (((X30) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X32 @ X30)
% 0.20/0.53          | ((sk_B_1 @ X30) != (k4_mcart_1 @ X32 @ X31 @ X33 @ X34)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (((X0) != (k4_mcart_1 @ X4 @ X3 @ X2 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X4 @ (k1_tarski @ X0))
% 0.20/0.53          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (((k1_tarski @ (k4_mcart_1 @ X4 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X4 @ (k1_tarski @ (k4_mcart_1 @ X4 @ X3 @ X2 @ X1))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['83'])).
% 0.20/0.53  thf('85', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ~ (r2_hidden @ X4 @ (k1_tarski @ (k4_mcart_1 @ X4 @ X3 @ X2 @ X1)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.20/0.53          (k1_tarski @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['80', '86'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_E @ (k1_tarski @ sk_E)))
% 0.20/0.53         <= ((((sk_E) = (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['79', '87'])).
% 0.20/0.53  thf('89', plain, (![X2 : $i]: (r2_hidden @ X2 @ (k1_tarski @ X2))),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (~ (((sk_E) = (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))),
% 0.20/0.53      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      ((((sk_E) = (k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))) | 
% 0.20/0.53       (((sk_E) = (k8_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))) | 
% 0.20/0.53       (((sk_E) = (k10_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E))) | 
% 0.20/0.53       (((sk_E) = (k9_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))),
% 0.20/0.53      inference('split', [status(esa)], ['13'])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      ((((sk_E) = (k11_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D @ sk_E)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['52', '78', '90', '91'])).
% 0.20/0.53  thf('93', plain, (((sk_E) = (k2_mcart_1 @ sk_E))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['15', '92'])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      ((((k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2) @ sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_E) != (sk_E))
% 0.20/0.53        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '93'])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      ((((sk_D) = (k1_xboole_0))
% 0.20/0.53        | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2) @ sk_C_1)
% 0.20/0.53            = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['94'])).
% 0.20/0.53  thf('96', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      (((k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2) @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.20/0.53  thf(t113_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         (((X9) = (k1_xboole_0))
% 0.20/0.53          | ((X10) = (k1_xboole_0))
% 0.20/0.53          | ((k2_zfmisc_1 @ X10 @ X9) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['99'])).
% 0.20/0.53  thf('101', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('102', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         (((X9) = (k1_xboole_0))
% 0.20/0.53          | ((X10) = (k1_xboole_0))
% 0.20/0.53          | ((k2_zfmisc_1 @ X10 @ X9) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B_2) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.53  thf('105', plain, ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['104'])).
% 0.20/0.53  thf('106', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('107', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('108', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['105', '106', '107'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
