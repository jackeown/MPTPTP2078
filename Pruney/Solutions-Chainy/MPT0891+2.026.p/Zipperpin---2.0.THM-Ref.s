%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P54EkDNvck

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:36 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  175 (1290 expanded)
%              Number of leaves         :   30 ( 397 expanded)
%              Depth                    :   28
%              Number of atoms          : 1917 (27075 expanded)
%              Number of equality atoms :  274 (4389 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

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

thf('6',plain,(
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('9',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_enumset1 @ X1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( ( sk_B @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['0','18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X3 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('22',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

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

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
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

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X26 @ X27 @ X29 @ X28 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('26',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( sk_D_1
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X25
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ ( k6_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ ( k7_mcart_1 @ X22 @ X23 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X22 @ X23 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('36',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('40',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ sk_D_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','44','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['33','56'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ ( k4_tarski @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ) @ ( k2_mcart_1 @ sk_D_1 ) @ X0 )
        = ( k4_tarski @ sk_D_1 @ X0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['33','56'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X30 @ X31 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k1_mcart_1 @ sk_D_1 )
      = ( k4_tarski @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) @ X0 )
        = ( k4_tarski @ sk_D_1 @ X0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( k1_mcart_1 @ ( k4_tarski @ sk_D_1 @ X0 ) )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X30 @ X31 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('71',plain,
    ( ( sk_D_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ( ( sk_B @ X33 )
       != ( k4_tarski @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_1 )
        | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_D_1 ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( ( k1_enumset1 @ ( k1_mcart_1 @ sk_D_1 ) @ ( k1_mcart_1 @ sk_D_1 ) @ X0 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k1_enumset1 @ ( k1_mcart_1 @ sk_D_1 ) @ ( k1_mcart_1 @ sk_D_1 ) @ X0 ) )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['23','73'])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('76',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ X0 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ X0 ) )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_D_1 )
        | ( ( sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ X0 ) )
          = ( k1_mcart_1 @ sk_D_1 ) )
        | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','77'])).

thf('79',plain,
    ( ( ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 ) )
        = ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50'])).

thf('81',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('82',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55'])).

thf('84',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19
       != ( k2_mcart_1 @ X19 ) )
      | ( X19
       != ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_tarski @ X20 @ X21 )
     != ( k2_mcart_1 @ ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X30: $i,X32: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X30 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_tarski @ X20 @ X21 )
     != X21 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['0','18'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('94',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('95',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('96',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53','54','55'])).

thf('98',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) @ X0 )
        = ( k4_tarski @ sk_D_1 @ X0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('103',plain,
    ( ( ( k1_mcart_1 @ sk_D_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) @ X0 )
        = ( k4_tarski @ sk_D_1 @ X0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( k1_mcart_1 @ ( k4_tarski @ sk_D_1 @ X0 ) )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X30 @ X31 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('108',plain,
    ( ( sk_D_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ( ( sk_B @ X33 )
       != ( k4_tarski @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D_1 )
        | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_D_1 ) @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( ( k1_enumset1 @ ( k1_mcart_1 @ sk_D_1 ) @ ( k1_mcart_1 @ sk_D_1 ) @ X0 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k1_enumset1 @ ( k1_mcart_1 @ sk_D_1 ) @ ( k1_mcart_1 @ sk_D_1 ) @ X0 ) )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['93','110'])).

thf('112',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('113',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ X0 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ X0 ) )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_D_1 )
        | ( ( sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ X0 ) )
          = ( k1_mcart_1 @ sk_D_1 ) )
        | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['92','114'])).

thf('116',plain,
    ( ( ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 ) )
        = ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k1_mcart_1 @ sk_D_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('118',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r2_hidden @ X34 @ X33 )
      | ( ( sk_B @ X33 )
       != ( k4_tarski @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != ( k1_mcart_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( ( k1_mcart_1 @ sk_D_1 )
       != ( k1_mcart_1 @ sk_D_1 ) )
      | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_D_1 @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('122',plain,
    ( ( ( ( k1_mcart_1 @ sk_D_1 )
       != ( k1_mcart_1 @ sk_D_1 ) )
      | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('125',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('127',plain,(
    sk_D_1
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('129',plain,
    ( sk_D_1
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['91','127','128'])).

thf('130',plain,
    ( ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 ) )
      = ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference(simpl_trail,[status(thm)],['79','129'])).

thf('131',plain,
    ( ( ( k1_mcart_1 @ sk_D_1 )
      = ( k4_tarski @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('132',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ( ( sk_B @ X33 )
       != ( k4_tarski @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != ( k1_mcart_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( sk_D_1
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['91','127','128'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( k1_mcart_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k1_mcart_1 @ sk_D_1 )
     != ( k1_mcart_1 @ sk_D_1 ) )
    | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_D_1 @ ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('138',plain,
    ( ( ( k1_mcart_1 @ sk_D_1 )
     != ( k1_mcart_1 @ sk_D_1 ) )
    | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_tarski @ ( k1_mcart_1 @ sk_D_1 ) @ sk_D_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('141',plain,(
    r2_hidden @ sk_D_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('143',plain,(
    $false ),
    inference('sup-',[status(thm)],['141','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P54EkDNvck
% 0.13/0.36  % Computer   : n013.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:45:10 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.52/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.74  % Solved by: fo/fo7.sh
% 0.52/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.74  % done 403 iterations in 0.258s
% 0.52/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.74  % SZS output start Refutation
% 0.52/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.74  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.52/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.74  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.52/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.74  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.52/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.74  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.52/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.74  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.52/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.74  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.52/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.74  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.52/0.74  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.52/0.74  thf(t70_enumset1, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.52/0.74  thf('0', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('1', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('2', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf(d2_tarski, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.52/0.74       ( ![D:$i]:
% 0.52/0.74         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.52/0.74  thf('3', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.74         (((X1) != (X0))
% 0.52/0.74          | (r2_hidden @ X1 @ X2)
% 0.52/0.74          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d2_tarski])).
% 0.52/0.74  thf('4', plain,
% 0.52/0.74      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['3'])).
% 0.52/0.74  thf('5', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['2', '4'])).
% 0.52/0.74  thf(t9_mcart_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74          ( ![B:$i]:
% 0.52/0.74            ( ~( ( r2_hidden @ B @ A ) & 
% 0.52/0.74                 ( ![C:$i,D:$i]:
% 0.52/0.74                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.52/0.74                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.74  thf('6', plain,
% 0.52/0.74      (![X33 : $i]:
% 0.52/0.74         (((X33) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X33) @ X33))),
% 0.52/0.74      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.52/0.74  thf('7', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('8', plain,
% 0.52/0.74      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.74          | ((X4) = (X3))
% 0.52/0.74          | ((X4) = (X0))
% 0.52/0.74          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d2_tarski])).
% 0.52/0.74  thf('9', plain,
% 0.52/0.74      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.52/0.74         (((X4) = (X0))
% 0.52/0.74          | ((X4) = (X3))
% 0.52/0.74          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.74  thf('10', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.52/0.74          | ((X2) = (X1))
% 0.52/0.74          | ((X2) = (X0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['7', '9'])).
% 0.52/0.74  thf('11', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((k1_enumset1 @ X1 @ X1 @ X0) = (k1_xboole_0))
% 0.52/0.74          | ((sk_B @ (k1_enumset1 @ X1 @ X1 @ X0)) = (X0))
% 0.52/0.74          | ((sk_B @ (k1_enumset1 @ X1 @ X1 @ X0)) = (X1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['6', '10'])).
% 0.52/0.74  thf(t113_zfmisc_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.74  thf('12', plain,
% 0.52/0.74      (![X9 : $i, X10 : $i]:
% 0.52/0.74         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.74  thf('13', plain,
% 0.52/0.74      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['12'])).
% 0.52/0.74  thf(t152_zfmisc_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.52/0.74  thf('14', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.52/0.74      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.52/0.74  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.74  thf('16', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.52/0.74          | ((sk_B @ (k1_enumset1 @ X1 @ X1 @ X0)) = (X1))
% 0.52/0.74          | ((sk_B @ (k1_enumset1 @ X1 @ X1 @ X0)) = (X0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['11', '15'])).
% 0.52/0.74  thf('17', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((sk_B @ (k1_enumset1 @ X1 @ X1 @ X0)) = (X0))
% 0.52/0.74          | ((sk_B @ (k1_enumset1 @ X1 @ X1 @ X0)) = (X1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['5', '16'])).
% 0.52/0.74  thf('18', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((sk_B @ (k2_tarski @ X1 @ X0)) = (X0))
% 0.52/0.74          | ((sk_B @ (k1_enumset1 @ X1 @ X1 @ X0)) = (X1)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['1', '17'])).
% 0.52/0.74  thf('19', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.52/0.74          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['0', '18'])).
% 0.52/0.74  thf('20', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('21', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.74         (((X1) != (X3))
% 0.52/0.74          | (r2_hidden @ X1 @ X2)
% 0.52/0.74          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d2_tarski])).
% 0.52/0.74  thf('22', plain,
% 0.52/0.74      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['21'])).
% 0.52/0.74  thf('23', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['20', '22'])).
% 0.52/0.74  thf(t51_mcart_1, conjecture,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74          ( ~( ![D:$i]:
% 0.52/0.74               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.74                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.52/0.74                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.52/0.74                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.52/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.74        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74             ( ~( ![D:$i]:
% 0.52/0.74                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.74                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.52/0.74                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.52/0.74                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.52/0.74    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.52/0.74  thf('24', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(t50_mcart_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74          ( ~( ![D:$i]:
% 0.52/0.74               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.74                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.52/0.74                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.52/0.74                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.52/0.74                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.52/0.74                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.52/0.74  thf('25', plain,
% 0.52/0.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.74         (((X26) = (k1_xboole_0))
% 0.52/0.74          | ((X27) = (k1_xboole_0))
% 0.52/0.74          | ((k5_mcart_1 @ X26 @ X27 @ X29 @ X28)
% 0.52/0.74              = (k1_mcart_1 @ (k1_mcart_1 @ X28)))
% 0.52/0.74          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X26 @ X27 @ X29))
% 0.52/0.74          | ((X29) = (k1_xboole_0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.52/0.74  thf('26', plain,
% 0.52/0.74      ((((sk_C) = (k1_xboole_0))
% 0.52/0.74        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.52/0.74            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.52/0.74        | ((sk_B_1) = (k1_xboole_0))
% 0.52/0.74        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('28', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('30', plain,
% 0.52/0.74      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.52/0.74         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.52/0.74  thf('31', plain,
% 0.52/0.74      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.52/0.74        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.52/0.74        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('32', plain,
% 0.52/0.74      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('split', [status(esa)], ['31'])).
% 0.52/0.74  thf('33', plain,
% 0.52/0.74      ((((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['30', '32'])).
% 0.52/0.74  thf('34', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(t48_mcart_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74          ( ~( ![D:$i]:
% 0.52/0.74               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.74                 ( ( D ) =
% 0.52/0.74                   ( k3_mcart_1 @
% 0.52/0.74                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.52/0.74                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.52/0.74                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.52/0.74  thf('35', plain,
% 0.52/0.74      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.52/0.74         (((X22) = (k1_xboole_0))
% 0.52/0.74          | ((X23) = (k1_xboole_0))
% 0.52/0.74          | ((X25)
% 0.52/0.74              = (k3_mcart_1 @ (k5_mcart_1 @ X22 @ X23 @ X24 @ X25) @ 
% 0.52/0.74                 (k6_mcart_1 @ X22 @ X23 @ X24 @ X25) @ 
% 0.52/0.74                 (k7_mcart_1 @ X22 @ X23 @ X24 @ X25)))
% 0.52/0.74          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X22 @ X23 @ X24))
% 0.52/0.74          | ((X24) = (k1_xboole_0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.52/0.74  thf('36', plain,
% 0.52/0.74      ((((sk_C) = (k1_xboole_0))
% 0.52/0.74        | ((sk_D_1)
% 0.52/0.74            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.52/0.74               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.52/0.74               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.52/0.74        | ((sk_B_1) = (k1_xboole_0))
% 0.52/0.74        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.74  thf('37', plain,
% 0.52/0.74      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.52/0.74         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['26', '27', '28', '29'])).
% 0.52/0.74  thf('38', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('39', plain,
% 0.52/0.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.74         (((X26) = (k1_xboole_0))
% 0.52/0.74          | ((X27) = (k1_xboole_0))
% 0.52/0.74          | ((k6_mcart_1 @ X26 @ X27 @ X29 @ X28)
% 0.52/0.74              = (k2_mcart_1 @ (k1_mcart_1 @ X28)))
% 0.52/0.74          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X26 @ X27 @ X29))
% 0.52/0.74          | ((X29) = (k1_xboole_0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.52/0.74  thf('40', plain,
% 0.52/0.74      ((((sk_C) = (k1_xboole_0))
% 0.52/0.74        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.52/0.74            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.52/0.74        | ((sk_B_1) = (k1_xboole_0))
% 0.52/0.74        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.74  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('43', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('44', plain,
% 0.52/0.74      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.52/0.74         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.52/0.74  thf('45', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('46', plain,
% 0.52/0.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.74         (((X26) = (k1_xboole_0))
% 0.52/0.74          | ((X27) = (k1_xboole_0))
% 0.52/0.74          | ((k7_mcart_1 @ X26 @ X27 @ X29 @ X28) = (k2_mcart_1 @ X28))
% 0.52/0.74          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X26 @ X27 @ X29))
% 0.52/0.74          | ((X29) = (k1_xboole_0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.52/0.74  thf('47', plain,
% 0.52/0.74      ((((sk_C) = (k1_xboole_0))
% 0.52/0.74        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))
% 0.52/0.74        | ((sk_B_1) = (k1_xboole_0))
% 0.52/0.74        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.74  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('49', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('51', plain,
% 0.52/0.74      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['47', '48', '49', '50'])).
% 0.52/0.74  thf('52', plain,
% 0.52/0.74      ((((sk_C) = (k1_xboole_0))
% 0.52/0.74        | ((sk_D_1)
% 0.52/0.74            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.52/0.74               (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))
% 0.52/0.74        | ((sk_B_1) = (k1_xboole_0))
% 0.52/0.74        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.74      inference('demod', [status(thm)], ['36', '37', '44', '51'])).
% 0.52/0.74  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('54', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('56', plain,
% 0.52/0.74      (((sk_D_1)
% 0.52/0.74         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.52/0.74            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['52', '53', '54', '55'])).
% 0.52/0.74  thf('57', plain,
% 0.52/0.74      ((((sk_D_1)
% 0.52/0.74          = (k3_mcart_1 @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.52/0.74             (k2_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['33', '56'])).
% 0.52/0.74  thf(d3_mcart_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.52/0.74  thf('58', plain,
% 0.52/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.74         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 0.52/0.74           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.52/0.74      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.52/0.74  thf('59', plain,
% 0.52/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.74         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 0.52/0.74           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.52/0.74      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.52/0.74  thf('60', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.74         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.52/0.74           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.52/0.74      inference('sup+', [status(thm)], ['58', '59'])).
% 0.52/0.74  thf('61', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          ((k3_mcart_1 @ 
% 0.52/0.74            (k4_tarski @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))) @ 
% 0.52/0.74            (k2_mcart_1 @ sk_D_1) @ X0) = (k4_tarski @ sk_D_1 @ X0)))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['57', '60'])).
% 0.52/0.74  thf('62', plain,
% 0.52/0.74      ((((sk_D_1)
% 0.52/0.74          = (k3_mcart_1 @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.52/0.74             (k2_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['33', '56'])).
% 0.52/0.74  thf('63', plain,
% 0.52/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.74         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 0.52/0.74           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.52/0.74      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.52/0.74  thf(t7_mcart_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.52/0.74       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.52/0.74  thf('64', plain,
% 0.52/0.74      (![X30 : $i, X31 : $i]: ((k1_mcart_1 @ (k4_tarski @ X30 @ X31)) = (X30))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.52/0.74  thf('65', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.52/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.52/0.74  thf('66', plain,
% 0.52/0.74      ((((k1_mcart_1 @ sk_D_1)
% 0.52/0.74          = (k4_tarski @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['62', '65'])).
% 0.52/0.74  thf('67', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          ((k3_mcart_1 @ (k1_mcart_1 @ sk_D_1) @ (k2_mcart_1 @ sk_D_1) @ X0)
% 0.52/0.74            = (k4_tarski @ sk_D_1 @ X0)))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('demod', [status(thm)], ['61', '66'])).
% 0.52/0.74  thf('68', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.52/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.52/0.74  thf('69', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          ((k1_mcart_1 @ (k4_tarski @ sk_D_1 @ X0))
% 0.52/0.74            = (k4_tarski @ (k1_mcart_1 @ sk_D_1) @ (k2_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['67', '68'])).
% 0.52/0.74  thf('70', plain,
% 0.52/0.74      (![X30 : $i, X31 : $i]: ((k1_mcart_1 @ (k4_tarski @ X30 @ X31)) = (X30))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.52/0.74  thf('71', plain,
% 0.52/0.74      ((((sk_D_1) = (k4_tarski @ (k1_mcart_1 @ sk_D_1) @ (k2_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.74  thf('72', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.74         (((X33) = (k1_xboole_0))
% 0.52/0.74          | ~ (r2_hidden @ X35 @ X33)
% 0.52/0.74          | ((sk_B @ X33) != (k4_tarski @ X35 @ X34)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.52/0.74  thf('73', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((sk_B @ X0) != (sk_D_1))
% 0.52/0.74           | ~ (r2_hidden @ (k1_mcart_1 @ sk_D_1) @ X0)
% 0.52/0.74           | ((X0) = (k1_xboole_0))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['71', '72'])).
% 0.52/0.74  thf('74', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((k1_enumset1 @ (k1_mcart_1 @ sk_D_1) @ (k1_mcart_1 @ sk_D_1) @ X0)
% 0.52/0.74             = (k1_xboole_0))
% 0.52/0.74           | ((sk_B @ 
% 0.52/0.74               (k1_enumset1 @ (k1_mcart_1 @ sk_D_1) @ (k1_mcart_1 @ sk_D_1) @ 
% 0.52/0.74                X0))
% 0.52/0.74               != (sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['23', '73'])).
% 0.52/0.74  thf('75', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('76', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('77', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ X0) = (k1_xboole_0))
% 0.52/0.74           | ((sk_B @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ X0)) != (sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.52/0.74  thf('78', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((X0) != (sk_D_1))
% 0.52/0.74           | ((sk_B @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ X0))
% 0.52/0.74               = (k1_mcart_1 @ sk_D_1))
% 0.52/0.74           | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ X0) = (k1_xboole_0))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['19', '77'])).
% 0.52/0.74  thf('79', plain,
% 0.52/0.74      (((((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74         | ((sk_B @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1))
% 0.52/0.74             = (k1_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['78'])).
% 0.52/0.74  thf('80', plain,
% 0.52/0.74      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['47', '48', '49', '50'])).
% 0.52/0.74  thf('81', plain,
% 0.52/0.74      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.52/0.74         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('split', [status(esa)], ['31'])).
% 0.52/0.74  thf('82', plain,
% 0.52/0.74      ((((sk_D_1) = (k2_mcart_1 @ sk_D_1)))
% 0.52/0.74         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['80', '81'])).
% 0.52/0.74  thf('83', plain,
% 0.52/0.74      (((sk_D_1)
% 0.52/0.74         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.52/0.74            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['52', '53', '54', '55'])).
% 0.52/0.74  thf('84', plain,
% 0.52/0.74      ((((sk_D_1)
% 0.52/0.74          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.52/0.74             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.52/0.74         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['82', '83'])).
% 0.52/0.74  thf('85', plain,
% 0.52/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.74         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 0.52/0.74           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.52/0.74      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.52/0.74  thf(t20_mcart_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.52/0.74       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.52/0.74  thf('86', plain,
% 0.52/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.74         (((X19) != (k2_mcart_1 @ X19)) | ((X19) != (k4_tarski @ X20 @ X21)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.52/0.74  thf('87', plain,
% 0.52/0.74      (![X20 : $i, X21 : $i]:
% 0.52/0.74         ((k4_tarski @ X20 @ X21) != (k2_mcart_1 @ (k4_tarski @ X20 @ X21)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['86'])).
% 0.52/0.74  thf('88', plain,
% 0.52/0.74      (![X30 : $i, X32 : $i]: ((k2_mcart_1 @ (k4_tarski @ X30 @ X32)) = (X32))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.52/0.74  thf('89', plain, (![X20 : $i, X21 : $i]: ((k4_tarski @ X20 @ X21) != (X21))),
% 0.52/0.74      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.74  thf('90', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['85', '89'])).
% 0.52/0.74  thf('91', plain,
% 0.52/0.74      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['84', '90'])).
% 0.52/0.74  thf('92', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.52/0.74          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['0', '18'])).
% 0.52/0.74  thf('93', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['20', '22'])).
% 0.52/0.74  thf('94', plain,
% 0.52/0.74      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.52/0.74         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.52/0.74  thf('95', plain,
% 0.52/0.74      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('split', [status(esa)], ['31'])).
% 0.52/0.74  thf('96', plain,
% 0.52/0.74      ((((sk_D_1) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['94', '95'])).
% 0.52/0.74  thf('97', plain,
% 0.52/0.74      (((sk_D_1)
% 0.52/0.74         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.52/0.74            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['52', '53', '54', '55'])).
% 0.52/0.74  thf('98', plain,
% 0.52/0.74      ((((sk_D_1)
% 0.52/0.74          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1 @ 
% 0.52/0.74             (k2_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['96', '97'])).
% 0.52/0.74  thf('99', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.74         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.52/0.74           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.52/0.74      inference('sup+', [status(thm)], ['58', '59'])).
% 0.52/0.74  thf('100', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          ((k3_mcart_1 @ 
% 0.52/0.74            (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1) @ 
% 0.52/0.74            (k2_mcart_1 @ sk_D_1) @ X0) = (k4_tarski @ sk_D_1 @ X0)))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['98', '99'])).
% 0.52/0.74  thf('101', plain,
% 0.52/0.74      ((((sk_D_1)
% 0.52/0.74          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1 @ 
% 0.52/0.74             (k2_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['96', '97'])).
% 0.52/0.74  thf('102', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.52/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.52/0.74  thf('103', plain,
% 0.52/0.74      ((((k1_mcart_1 @ sk_D_1)
% 0.52/0.74          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['101', '102'])).
% 0.52/0.74  thf('104', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          ((k3_mcart_1 @ (k1_mcart_1 @ sk_D_1) @ (k2_mcart_1 @ sk_D_1) @ X0)
% 0.52/0.74            = (k4_tarski @ sk_D_1 @ X0)))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('demod', [status(thm)], ['100', '103'])).
% 0.52/0.74  thf('105', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.52/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.52/0.74  thf('106', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          ((k1_mcart_1 @ (k4_tarski @ sk_D_1 @ X0))
% 0.52/0.74            = (k4_tarski @ (k1_mcart_1 @ sk_D_1) @ (k2_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['104', '105'])).
% 0.52/0.74  thf('107', plain,
% 0.52/0.74      (![X30 : $i, X31 : $i]: ((k1_mcart_1 @ (k4_tarski @ X30 @ X31)) = (X30))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.52/0.74  thf('108', plain,
% 0.52/0.74      ((((sk_D_1) = (k4_tarski @ (k1_mcart_1 @ sk_D_1) @ (k2_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('demod', [status(thm)], ['106', '107'])).
% 0.52/0.74  thf('109', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.74         (((X33) = (k1_xboole_0))
% 0.52/0.74          | ~ (r2_hidden @ X35 @ X33)
% 0.52/0.74          | ((sk_B @ X33) != (k4_tarski @ X35 @ X34)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.52/0.74  thf('110', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((sk_B @ X0) != (sk_D_1))
% 0.52/0.74           | ~ (r2_hidden @ (k1_mcart_1 @ sk_D_1) @ X0)
% 0.52/0.74           | ((X0) = (k1_xboole_0))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['108', '109'])).
% 0.52/0.74  thf('111', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((k1_enumset1 @ (k1_mcart_1 @ sk_D_1) @ (k1_mcart_1 @ sk_D_1) @ X0)
% 0.52/0.74             = (k1_xboole_0))
% 0.52/0.74           | ((sk_B @ 
% 0.52/0.74               (k1_enumset1 @ (k1_mcart_1 @ sk_D_1) @ (k1_mcart_1 @ sk_D_1) @ 
% 0.52/0.74                X0))
% 0.52/0.74               != (sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['93', '110'])).
% 0.52/0.74  thf('112', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('113', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('114', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ X0) = (k1_xboole_0))
% 0.52/0.74           | ((sk_B @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ X0)) != (sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.52/0.74  thf('115', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((X0) != (sk_D_1))
% 0.52/0.74           | ((sk_B @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ X0))
% 0.52/0.74               = (k1_mcart_1 @ sk_D_1))
% 0.52/0.74           | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ X0) = (k1_xboole_0))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['92', '114'])).
% 0.52/0.74  thf('116', plain,
% 0.52/0.74      (((((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74         | ((sk_B @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1))
% 0.52/0.74             = (k1_mcart_1 @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['115'])).
% 0.52/0.74  thf('117', plain,
% 0.52/0.74      ((((k1_mcart_1 @ sk_D_1)
% 0.52/0.74          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['101', '102'])).
% 0.52/0.74  thf('118', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.74         (((X33) = (k1_xboole_0))
% 0.52/0.74          | ~ (r2_hidden @ X34 @ X33)
% 0.52/0.74          | ((sk_B @ X33) != (k4_tarski @ X35 @ X34)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.52/0.74  thf('119', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((sk_B @ X0) != (k1_mcart_1 @ sk_D_1))
% 0.52/0.74           | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.52/0.74           | ((X0) = (k1_xboole_0))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['117', '118'])).
% 0.52/0.74  thf('120', plain,
% 0.52/0.74      (((((k1_mcart_1 @ sk_D_1) != (k1_mcart_1 @ sk_D_1))
% 0.52/0.74         | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74         | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74         | ~ (r2_hidden @ sk_D_1 @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['116', '119'])).
% 0.52/0.74  thf('121', plain,
% 0.52/0.74      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['3'])).
% 0.52/0.74  thf('122', plain,
% 0.52/0.74      (((((k1_mcart_1 @ sk_D_1) != (k1_mcart_1 @ sk_D_1))
% 0.52/0.74         | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74         | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('demod', [status(thm)], ['120', '121'])).
% 0.52/0.74  thf('123', plain,
% 0.52/0.74      ((((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0)))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['122'])).
% 0.52/0.74  thf('124', plain,
% 0.52/0.74      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['3'])).
% 0.52/0.74  thf('125', plain,
% 0.52/0.74      (((r2_hidden @ sk_D_1 @ k1_xboole_0))
% 0.52/0.74         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['123', '124'])).
% 0.52/0.74  thf('126', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.74  thf('127', plain,
% 0.52/0.74      (~ (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['125', '126'])).
% 0.52/0.74  thf('128', plain,
% 0.52/0.74      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.52/0.74       (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.52/0.74       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.52/0.74      inference('split', [status(esa)], ['31'])).
% 0.52/0.74  thf('129', plain,
% 0.52/0.74      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.52/0.74      inference('sat_resolution*', [status(thm)], ['91', '127', '128'])).
% 0.52/0.74  thf('130', plain,
% 0.52/0.74      ((((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74        | ((sk_B @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1))
% 0.52/0.74            = (k1_mcart_1 @ sk_D_1)))),
% 0.52/0.74      inference('simpl_trail', [status(thm)], ['79', '129'])).
% 0.52/0.74  thf('131', plain,
% 0.52/0.74      ((((k1_mcart_1 @ sk_D_1)
% 0.52/0.74          = (k4_tarski @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['62', '65'])).
% 0.52/0.74  thf('132', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.74         (((X33) = (k1_xboole_0))
% 0.52/0.74          | ~ (r2_hidden @ X35 @ X33)
% 0.52/0.74          | ((sk_B @ X33) != (k4_tarski @ X35 @ X34)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.52/0.74  thf('133', plain,
% 0.52/0.74      ((![X0 : $i]:
% 0.52/0.74          (((sk_B @ X0) != (k1_mcart_1 @ sk_D_1))
% 0.52/0.74           | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.52/0.74           | ((X0) = (k1_xboole_0))))
% 0.52/0.74         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['131', '132'])).
% 0.52/0.74  thf('134', plain,
% 0.52/0.74      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.52/0.74      inference('sat_resolution*', [status(thm)], ['91', '127', '128'])).
% 0.52/0.74  thf('135', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((sk_B @ X0) != (k1_mcart_1 @ sk_D_1))
% 0.52/0.74          | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.52/0.74          | ((X0) = (k1_xboole_0)))),
% 0.52/0.74      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 0.52/0.74  thf('136', plain,
% 0.52/0.74      ((((k1_mcart_1 @ sk_D_1) != (k1_mcart_1 @ sk_D_1))
% 0.52/0.74        | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74        | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74        | ~ (r2_hidden @ sk_D_1 @ (k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['130', '135'])).
% 0.52/0.74  thf('137', plain,
% 0.52/0.74      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['3'])).
% 0.52/0.74  thf('138', plain,
% 0.52/0.74      ((((k1_mcart_1 @ sk_D_1) != (k1_mcart_1 @ sk_D_1))
% 0.52/0.74        | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74        | ((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('demod', [status(thm)], ['136', '137'])).
% 0.52/0.74  thf('139', plain,
% 0.52/0.74      (((k2_tarski @ (k1_mcart_1 @ sk_D_1) @ sk_D_1) = (k1_xboole_0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['138'])).
% 0.52/0.74  thf('140', plain,
% 0.52/0.74      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['3'])).
% 0.52/0.74  thf('141', plain, ((r2_hidden @ sk_D_1 @ k1_xboole_0)),
% 0.52/0.74      inference('sup+', [status(thm)], ['139', '140'])).
% 0.52/0.74  thf('142', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.74  thf('143', plain, ($false), inference('sup-', [status(thm)], ['141', '142'])).
% 0.52/0.74  
% 0.52/0.74  % SZS output end Refutation
% 0.52/0.74  
% 0.52/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
