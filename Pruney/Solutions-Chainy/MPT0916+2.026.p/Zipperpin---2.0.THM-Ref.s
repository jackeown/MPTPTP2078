%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7XPBaSd7D7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:08 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 538 expanded)
%              Number of leaves         :   31 ( 179 expanded)
%              Depth                    :   27
%              Number of atoms          : 1285 (7608 expanded)
%              Number of equality atoms :   78 ( 129 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t76_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
     => ! [E: $i] :
          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
         => ! [F: $i] :
              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                 => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                   => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                      & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                      & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
       => ! [E: $i] :
            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
               => ! [G: $i] :
                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                   => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                     => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                        & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                        & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
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

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
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

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('16',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('21',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['17'])).

thf('23',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('25',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 )
      | ( r1_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_F @ X0 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_F @ X0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_F @ X0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['38','41'])).

thf('44',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_F @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 )
      | ( r1_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_E @ X0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_E @ X0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('58',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['56','57'])).

thf('60',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('65',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('68',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_xboole_0 @ sk_D @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('77',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k2_mcart_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('80',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('82',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['38','41'])).

thf('84',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_F @ X0 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_F @ X0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ sk_F @ X0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('90',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('92',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('94',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('95',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_xboole_0 @ sk_E @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_E @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('102',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('104',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('106',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['17'])).

thf('108',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['77','106','107'])).

thf('109',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['18','108'])).

thf('110',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','109'])).

thf('111',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['56','57'])).

thf('112',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_F @ X0 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('118',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('124',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('127',plain,(
    r1_xboole_0 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['10','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7XPBaSd7D7
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 250 iterations in 0.093s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.37/0.55  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.55  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.37/0.55  thf(t76_mcart_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ![E:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.37/0.55           ( ![F:$i]:
% 0.37/0.55             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.37/0.55               ( ![G:$i]:
% 0.37/0.55                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.55                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.37/0.55                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.37/0.55                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.37/0.55                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55          ( ![E:$i]:
% 0.37/0.55            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.37/0.55              ( ![F:$i]:
% 0.37/0.55                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.37/0.55                  ( ![G:$i]:
% 0.37/0.55                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.55                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.37/0.55                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.37/0.55                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.37/0.55                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.37/0.55  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d3_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.37/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.37/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.37/0.55  thf(t10_mcart_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.37/0.55       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.37/0.55         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.37/0.55          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.37/0.55          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.37/0.55          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('7', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf(t3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.55          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.37/0.55          | ~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf('10', plain, (~ (r1_xboole_0 @ sk_D @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.37/0.55  thf('11', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t3_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('13', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t50_mcart_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ~( ![D:$i]:
% 0.37/0.55               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.55                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.37/0.55                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.37/0.55                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.37/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.37/0.55                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.55         (((X23) = (k1_xboole_0))
% 0.37/0.55          | ((X24) = (k1_xboole_0))
% 0.37/0.55          | ((k6_mcart_1 @ X23 @ X24 @ X26 @ X25)
% 0.37/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X25)))
% 0.37/0.55          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.37/0.55          | ((X26) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      ((((sk_C_1) = (k1_xboole_0))
% 0.37/0.55        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.37/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)
% 0.37/0.55        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)
% 0.37/0.55        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.37/0.55      inference('split', [status(esa)], ['17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.55         (((X23) = (k1_xboole_0))
% 0.37/0.55          | ((X24) = (k1_xboole_0))
% 0.37/0.55          | ((k5_mcart_1 @ X23 @ X24 @ X26 @ X25)
% 0.37/0.55              = (k1_mcart_1 @ (k1_mcart_1 @ X25)))
% 0.37/0.55          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.37/0.55          | ((X26) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((((sk_C_1) = (k1_xboole_0))
% 0.37/0.55        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.37/0.55            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('split', [status(esa)], ['17'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C_1) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C_1) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.55  thf('26', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('28', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf(t63_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.37/0.55       ( r1_xboole_0 @ A @ C ) ))).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X5 @ X6)
% 0.37/0.55          | ~ (r1_xboole_0 @ X6 @ X7)
% 0.37/0.55          | (r1_xboole_0 @ X5 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X0 : $i]: ((r1_xboole_0 @ sk_F @ X0) | ~ (r1_xboole_0 @ sk_C_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55           | ((sk_B) = (k1_xboole_0))
% 0.37/0.55           | ((sk_A) = (k1_xboole_0))
% 0.37/0.55           | (r1_xboole_0 @ sk_F @ X0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '30'])).
% 0.37/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.55  thf('32', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf(t7_ordinal1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_tarski @ X0 @ (sk_C @ X1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (((sk_B) = (k1_xboole_0))
% 0.37/0.55           | ((sk_A) = (k1_xboole_0))
% 0.37/0.55           | (r1_xboole_0 @ sk_F @ X0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('demod', [status(thm)], ['31', '36'])).
% 0.37/0.55  thf('38', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.37/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.55         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.37/0.55          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.37/0.55          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['38', '41'])).
% 0.37/0.55  thf('43', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['38', '41'])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.55          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ sk_F @ X0)
% 0.37/0.55          | ~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.55  thf('46', plain, (~ (r1_xboole_0 @ sk_F @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['42', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['37', '46'])).
% 0.37/0.55  thf('48', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('50', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X5 @ X6)
% 0.37/0.55          | ~ (r1_xboole_0 @ X6 @ X7)
% 0.37/0.55          | (r1_xboole_0 @ X5 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X0 : $i]: ((r1_xboole_0 @ sk_E @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55           | ((sk_A) = (k1_xboole_0))
% 0.37/0.55           | (r1_xboole_0 @ sk_E @ X0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '52'])).
% 0.37/0.55  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_xboole_0 @ sk_E @ X0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('demod', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.55         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.37/0.55          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('58', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('59', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.55          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ sk_E @ X0)
% 0.37/0.55          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.55  thf('62', plain, (~ (r1_xboole_0 @ sk_E @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['58', '61'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['55', '62'])).
% 0.37/0.55  thf('64', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['63', '64'])).
% 0.37/0.55  thf('66', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.55  thf('70', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['66', '69'])).
% 0.37/0.55  thf('71', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf(t64_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.37/0.55         ( r1_xboole_0 @ B @ D ) ) =>
% 0.37/0.55       ( r1_xboole_0 @ A @ C ) ))).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X8 @ X9)
% 0.37/0.55          | ~ (r1_tarski @ X8 @ X10)
% 0.37/0.55          | ~ (r1_tarski @ X9 @ X11)
% 0.37/0.55          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ sk_A @ X0)
% 0.37/0.55          | ~ (r1_tarski @ X1 @ X0)
% 0.37/0.55          | (r1_xboole_0 @ sk_D @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.55  thf('74', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ sk_D @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['70', '73'])).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_D @ sk_D))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['65', '74'])).
% 0.37/0.55  thf('76', plain, (~ (r1_xboole_0 @ sk_D @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.37/0.55  thf('77', plain,
% 0.37/0.55      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.55  thf('78', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('79', plain,
% 0.37/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.55         (((X23) = (k1_xboole_0))
% 0.37/0.55          | ((X24) = (k1_xboole_0))
% 0.37/0.55          | ((k7_mcart_1 @ X23 @ X24 @ X26 @ X25) = (k2_mcart_1 @ X25))
% 0.37/0.55          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.37/0.55          | ((X26) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.37/0.55  thf('80', plain,
% 0.37/0.55      ((((sk_C_1) = (k1_xboole_0))
% 0.37/0.55        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['78', '79'])).
% 0.37/0.55  thf('81', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('split', [status(esa)], ['17'])).
% 0.37/0.55  thf('82', plain,
% 0.37/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C_1) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.55  thf('83', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['38', '41'])).
% 0.37/0.55  thf('84', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C_1) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('demod', [status(thm)], ['82', '83'])).
% 0.37/0.55  thf('85', plain,
% 0.37/0.55      (![X0 : $i]: ((r1_xboole_0 @ sk_F @ X0) | ~ (r1_xboole_0 @ sk_C_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('86', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55           | ((sk_B) = (k1_xboole_0))
% 0.37/0.55           | ((sk_A) = (k1_xboole_0))
% 0.37/0.55           | (r1_xboole_0 @ sk_F @ X0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.37/0.55  thf('87', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.55  thf('88', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (((sk_B) = (k1_xboole_0))
% 0.37/0.55           | ((sk_A) = (k1_xboole_0))
% 0.37/0.55           | (r1_xboole_0 @ sk_F @ X0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.55  thf('89', plain, (~ (r1_xboole_0 @ sk_F @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['42', '45'])).
% 0.37/0.55  thf('90', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['88', '89'])).
% 0.37/0.55  thf('91', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.55  thf('92', plain,
% 0.37/0.55      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['90', '91'])).
% 0.37/0.55  thf('93', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['66', '69'])).
% 0.37/0.55  thf('94', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.55  thf('95', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X8 @ X9)
% 0.37/0.55          | ~ (r1_tarski @ X8 @ X10)
% 0.37/0.55          | ~ (r1_tarski @ X9 @ X11)
% 0.37/0.55          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.37/0.55  thf('96', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.37/0.55          | ~ (r1_tarski @ X1 @ X0)
% 0.37/0.55          | (r1_xboole_0 @ sk_E @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.37/0.55  thf('97', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ sk_E @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['93', '96'])).
% 0.37/0.55  thf('98', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0)) | (r1_xboole_0 @ sk_E @ sk_E)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['92', '97'])).
% 0.37/0.55  thf('99', plain, (~ (r1_xboole_0 @ sk_E @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['58', '61'])).
% 0.37/0.55  thf('100', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('clc', [status(thm)], ['98', '99'])).
% 0.37/0.55  thf('101', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('102', plain,
% 0.37/0.55      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['100', '101'])).
% 0.37/0.55  thf('103', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ sk_D @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['70', '73'])).
% 0.37/0.55  thf('104', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_D @ sk_D))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['102', '103'])).
% 0.37/0.55  thf('105', plain, (~ (r1_xboole_0 @ sk_D @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.37/0.55  thf('106', plain,
% 0.37/0.55      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['104', '105'])).
% 0.37/0.55  thf('107', plain,
% 0.37/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.37/0.55       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.37/0.55       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))),
% 0.37/0.55      inference('split', [status(esa)], ['17'])).
% 0.37/0.55  thf('108', plain,
% 0.37/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['77', '106', '107'])).
% 0.37/0.55  thf('109', plain,
% 0.37/0.55      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['18', '108'])).
% 0.37/0.55  thf('110', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_C_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '109'])).
% 0.37/0.55  thf('111', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('112', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_C_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['110', '111'])).
% 0.37/0.55  thf('113', plain,
% 0.37/0.55      (![X0 : $i]: ((r1_xboole_0 @ sk_F @ X0) | ~ (r1_xboole_0 @ sk_C_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('114', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55          | ((sk_B) = (k1_xboole_0))
% 0.37/0.55          | ((sk_A) = (k1_xboole_0))
% 0.37/0.55          | (r1_xboole_0 @ sk_F @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['112', '113'])).
% 0.37/0.55  thf('115', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.55  thf('116', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((sk_B) = (k1_xboole_0))
% 0.37/0.55          | ((sk_A) = (k1_xboole_0))
% 0.37/0.55          | (r1_xboole_0 @ sk_F @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['114', '115'])).
% 0.37/0.55  thf('117', plain, (~ (r1_xboole_0 @ sk_F @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['42', '45'])).
% 0.37/0.55  thf('118', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['116', '117'])).
% 0.37/0.55  thf('119', plain,
% 0.37/0.55      (![X0 : $i]: ((r1_xboole_0 @ sk_E @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.55  thf('120', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55          | ((sk_A) = (k1_xboole_0))
% 0.37/0.55          | (r1_xboole_0 @ sk_E @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['118', '119'])).
% 0.37/0.55  thf('121', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.55  thf('122', plain,
% 0.37/0.55      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_xboole_0 @ sk_E @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['120', '121'])).
% 0.37/0.55  thf('123', plain, (~ (r1_xboole_0 @ sk_E @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['58', '61'])).
% 0.37/0.55  thf('124', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['122', '123'])).
% 0.37/0.55  thf('125', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.37/0.55      inference('demod', [status(thm)], ['13', '124'])).
% 0.37/0.55  thf('126', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ sk_D @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['70', '73'])).
% 0.37/0.55  thf('127', plain, ((r1_xboole_0 @ sk_D @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['125', '126'])).
% 0.37/0.55  thf('128', plain, ($false), inference('demod', [status(thm)], ['10', '127'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
