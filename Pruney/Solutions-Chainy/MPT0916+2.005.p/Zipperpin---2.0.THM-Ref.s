%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Abn6fpTIOE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:05 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 509 expanded)
%              Number of leaves         :   36 ( 171 expanded)
%              Depth                    :   23
%              Number of atoms          : 1161 (6073 expanded)
%              Number of equality atoms :   77 ( 150 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X12 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_G ) @ ( k1_zfmisc_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_G ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['24','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('36',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k2_mcart_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['37'])).

thf('43',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('46',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['44','47'])).

thf('51',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_E )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(condensation,[status(thm)],['62'])).

thf('64',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('70',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['63','72'])).

thf('74',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['59','73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','32'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('83',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['37'])).

thf('85',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('87',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('88',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('91',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,
    ( ( ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['63','72'])).

thf('95',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','32'])).

thf('99',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['37'])).

thf('103',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['80','101','102'])).

thf('104',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['38','103'])).

thf('105',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','104'])).

thf('106',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['68','69'])).

thf('107',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('109',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['63','72'])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['33','115','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Abn6fpTIOE
% 0.16/0.36  % Computer   : n005.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 09:26:03 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 305 iterations in 0.241s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.53/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.71  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.53/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i > $i).
% 0.53/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.71  thf(sk_G_type, type, sk_G: $i).
% 0.53/0.71  thf(sk_F_type, type, sk_F: $i).
% 0.53/0.71  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.53/0.71  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.53/0.71  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.53/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.71  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.53/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.71  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.53/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.71  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.53/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(t76_mcart_1, conjecture,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.71       ( ![E:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.53/0.71           ( ![F:$i]:
% 0.53/0.71             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.53/0.71               ( ![G:$i]:
% 0.53/0.71                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.53/0.71                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.53/0.71                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.53/0.71                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.53/0.71                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.71          ( ![E:$i]:
% 0.53/0.71            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.53/0.71              ( ![F:$i]:
% 0.53/0.71                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.53/0.71                  ( ![G:$i]:
% 0.53/0.71                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.53/0.71                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.53/0.71                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.53/0.71                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.53/0.71                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.53/0.71  thf('0', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t6_mcart_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.53/0.71          ( ![B:$i]:
% 0.53/0.71            ( ~( ( r2_hidden @ B @ A ) & 
% 0.53/0.71                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.53/0.71                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.53/0.71                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.53/0.71                       ( r2_hidden @ G @ B ) ) =>
% 0.53/0.71                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      (![X27 : $i]:
% 0.53/0.71         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X27) @ X27))),
% 0.53/0.71      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.53/0.71  thf(d1_xboole_0, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.53/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.71  thf('3', plain,
% 0.53/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.71  thf('4', plain,
% 0.53/0.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.53/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.71  thf(t10_mcart_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.53/0.71       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.53/0.71         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.53/0.71  thf('5', plain,
% 0.53/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.71         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.53/0.71          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.53/0.71          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.53/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.53/0.71  thf('7', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.53/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.71  thf('8', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf(cc3_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_xboole_0 @ A ) =>
% 0.53/0.71       ( ![C:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71           ( v1_xboole_0 @ C ) ) ) ))).
% 0.53/0.71  thf('11', plain,
% 0.53/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.71         (~ (v1_xboole_0 @ X14)
% 0.53/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 0.53/0.71          | (v1_xboole_0 @ X15))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      (![X1 : $i, X2 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.53/0.71          | ~ (v1_xboole_0 @ X1)
% 0.53/0.71          | (v1_xboole_0 @ X2)
% 0.53/0.71          | ~ (v1_xboole_0 @ X1))),
% 0.53/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.53/0.71  thf('13', plain,
% 0.53/0.71      (![X1 : $i, X2 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ X2)
% 0.53/0.71          | ~ (v1_xboole_0 @ X1)
% 0.53/0.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['12'])).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.53/0.71          | ~ (v1_xboole_0 @ X0)
% 0.53/0.71          | ~ (v1_xboole_0 @ X2)
% 0.53/0.71          | (v1_xboole_0 @ X1))),
% 0.53/0.71      inference('sup-', [status(thm)], ['3', '13'])).
% 0.53/0.71  thf('15', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['0', '14'])).
% 0.53/0.71  thf('16', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.53/0.71      inference('condensation', [status(thm)], ['15'])).
% 0.53/0.71  thf('17', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.53/0.71  thf('18', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t63_subset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( r2_hidden @ A @ B ) =>
% 0.53/0.71       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      (![X12 : $i, X13 : $i]:
% 0.53/0.71         ((m1_subset_1 @ (k1_tarski @ X12) @ (k1_zfmisc_1 @ X13))
% 0.53/0.71          | ~ (r2_hidden @ X12 @ X13))),
% 0.53/0.71      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      ((m1_subset_1 @ (k1_tarski @ sk_G) @ 
% 0.53/0.71        (k1_zfmisc_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.53/0.71  thf(d3_zfmisc_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.53/0.71       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.71         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.53/0.71           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.53/0.71      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.71  thf('22', plain,
% 0.53/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.71         (~ (v1_xboole_0 @ X14)
% 0.53/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 0.53/0.71          | (v1_xboole_0 @ X15))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.53/0.71  thf('23', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)))
% 0.53/0.71          | (v1_xboole_0 @ X3)
% 0.53/0.71          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.71  thf('24', plain,
% 0.53/0.71      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))
% 0.53/0.71        | (v1_xboole_0 @ (k1_tarski @ sk_G)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['20', '23'])).
% 0.53/0.71  thf(d10_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.71  thf('25', plain,
% 0.53/0.71      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.71  thf('26', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.53/0.71      inference('simplify', [status(thm)], ['25'])).
% 0.53/0.71  thf(l1_zfmisc_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.53/0.71  thf('27', plain,
% 0.53/0.71      (![X6 : $i, X7 : $i]:
% 0.53/0.71         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k1_tarski @ X6) @ X7))),
% 0.53/0.71      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.53/0.71  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.53/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.71  thf('30', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.53/0.71  thf('31', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.53/0.71      inference('clc', [status(thm)], ['24', '30'])).
% 0.53/0.71  thf('32', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.53/0.71      inference('sup-', [status(thm)], ['17', '31'])).
% 0.53/0.71  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.53/0.71      inference('clc', [status(thm)], ['16', '32'])).
% 0.53/0.71  thf('34', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t50_mcart_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.53/0.71          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.53/0.71          ( ~( ![D:$i]:
% 0.53/0.71               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.53/0.71                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.53/0.71                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.53/0.71                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.53/0.71                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.53/0.71                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.53/0.71  thf('35', plain,
% 0.53/0.71      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.71         (((X23) = (k1_xboole_0))
% 0.53/0.71          | ((X24) = (k1_xboole_0))
% 0.53/0.71          | ((k6_mcart_1 @ X23 @ X24 @ X26 @ X25)
% 0.53/0.71              = (k2_mcart_1 @ (k1_mcart_1 @ X25)))
% 0.53/0.71          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.53/0.71          | ((X26) = (k1_xboole_0)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.53/0.71  thf('36', plain,
% 0.53/0.71      ((((sk_C) = (k1_xboole_0))
% 0.53/0.71        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G)
% 0.53/0.71            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.53/0.71        | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.71  thf('37', plain,
% 0.53/0.71      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)
% 0.53/0.71        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_E)
% 0.53/0.71        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('38', plain,
% 0.53/0.71      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_E))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_E)))),
% 0.53/0.71      inference('split', [status(esa)], ['37'])).
% 0.53/0.71  thf('39', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('40', plain,
% 0.53/0.71      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.71         (((X23) = (k1_xboole_0))
% 0.53/0.71          | ((X24) = (k1_xboole_0))
% 0.53/0.71          | ((k7_mcart_1 @ X23 @ X24 @ X26 @ X25) = (k2_mcart_1 @ X25))
% 0.53/0.71          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.53/0.71          | ((X26) = (k1_xboole_0)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.53/0.71  thf('41', plain,
% 0.53/0.71      ((((sk_C) = (k1_xboole_0))
% 0.53/0.71        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.53/0.71        | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.71  thf('42', plain,
% 0.53/0.71      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F)))),
% 0.53/0.71      inference('split', [status(esa)], ['37'])).
% 0.53/0.71  thf('43', plain,
% 0.53/0.71      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.53/0.71         | ((sk_A) = (k1_xboole_0))
% 0.53/0.71         | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71         | ((sk_C) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.53/0.71  thf('44', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('45', plain,
% 0.53/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.71         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.53/0.71           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.53/0.71      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.71  thf('46', plain,
% 0.53/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.71         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.53/0.71          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.53/0.71  thf('47', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.53/0.71          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.53/0.71  thf('48', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.53/0.71      inference('sup-', [status(thm)], ['44', '47'])).
% 0.53/0.71  thf('49', plain,
% 0.53/0.71      (((((sk_A) = (k1_xboole_0))
% 0.53/0.71         | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71         | ((sk_C) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F)))),
% 0.53/0.71      inference('demod', [status(thm)], ['43', '48'])).
% 0.53/0.71  thf('50', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.53/0.71      inference('sup-', [status(thm)], ['44', '47'])).
% 0.53/0.71  thf('51', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(l3_subset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.53/0.71  thf('52', plain,
% 0.53/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X9 @ X10)
% 0.53/0.71          | (r2_hidden @ X9 @ X11)
% 0.53/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.53/0.71      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.53/0.71  thf('53', plain,
% 0.53/0.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.53/0.71      inference('sup-', [status(thm)], ['51', '52'])).
% 0.53/0.71  thf('54', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C)),
% 0.53/0.71      inference('sup-', [status(thm)], ['50', '53'])).
% 0.53/0.71  thf('55', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.53/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.71  thf('56', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.53/0.71  thf('57', plain,
% 0.53/0.71      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.71         | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71         | ((sk_A) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['49', '56'])).
% 0.53/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.71  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('59', plain,
% 0.53/0.71      (((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F)))),
% 0.53/0.71      inference('demod', [status(thm)], ['57', '58'])).
% 0.53/0.71  thf('60', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_2))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('61', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.53/0.71          | ~ (v1_xboole_0 @ X0)
% 0.53/0.71          | ~ (v1_xboole_0 @ X2)
% 0.53/0.71          | (v1_xboole_0 @ X1))),
% 0.53/0.71      inference('sup-', [status(thm)], ['3', '13'])).
% 0.53/0.71  thf('62', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ sk_E)
% 0.53/0.71          | ~ (v1_xboole_0 @ X0)
% 0.53/0.71          | ~ (v1_xboole_0 @ sk_B_2))),
% 0.53/0.71      inference('sup-', [status(thm)], ['60', '61'])).
% 0.53/0.71  thf('63', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.53/0.71      inference('condensation', [status(thm)], ['62'])).
% 0.53/0.71  thf('64', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('65', plain,
% 0.53/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.71         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.53/0.71           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.53/0.71      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.53/0.71  thf('66', plain,
% 0.53/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.71         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.53/0.71          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.53/0.71  thf('67', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.53/0.71          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['65', '66'])).
% 0.53/0.71  thf('68', plain,
% 0.53/0.71      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.53/0.71      inference('sup-', [status(thm)], ['64', '67'])).
% 0.53/0.71  thf('69', plain,
% 0.53/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.71         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.53/0.71          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.53/0.71  thf('70', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.53/0.71      inference('sup-', [status(thm)], ['68', '69'])).
% 0.53/0.71  thf('71', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.53/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.71  thf('72', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.53/0.71      inference('sup-', [status(thm)], ['70', '71'])).
% 0.53/0.71  thf('73', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.53/0.71      inference('clc', [status(thm)], ['63', '72'])).
% 0.53/0.71  thf('74', plain,
% 0.53/0.71      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['59', '73'])).
% 0.53/0.71  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('76', plain,
% 0.53/0.71      ((((sk_A) = (k1_xboole_0)))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F)))),
% 0.53/0.71      inference('demod', [status(thm)], ['74', '75'])).
% 0.53/0.71  thf('77', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.53/0.71      inference('clc', [status(thm)], ['16', '32'])).
% 0.53/0.71  thf('78', plain,
% 0.53/0.71      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['76', '77'])).
% 0.53/0.71  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('80', plain,
% 0.53/0.71      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F))),
% 0.53/0.71      inference('demod', [status(thm)], ['78', '79'])).
% 0.53/0.71  thf('81', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('82', plain,
% 0.53/0.71      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.71         (((X23) = (k1_xboole_0))
% 0.53/0.71          | ((X24) = (k1_xboole_0))
% 0.53/0.71          | ((k5_mcart_1 @ X23 @ X24 @ X26 @ X25)
% 0.53/0.71              = (k1_mcart_1 @ (k1_mcart_1 @ X25)))
% 0.53/0.71          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.53/0.71          | ((X26) = (k1_xboole_0)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.53/0.71  thf('83', plain,
% 0.53/0.71      ((((sk_C) = (k1_xboole_0))
% 0.53/0.71        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G)
% 0.53/0.71            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.53/0.71        | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['81', '82'])).
% 0.53/0.71  thf('84', plain,
% 0.53/0.71      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)))),
% 0.53/0.71      inference('split', [status(esa)], ['37'])).
% 0.53/0.71  thf('85', plain,
% 0.53/0.71      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.53/0.71         | ((sk_A) = (k1_xboole_0))
% 0.53/0.71         | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71         | ((sk_C) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['83', '84'])).
% 0.53/0.71  thf('86', plain,
% 0.53/0.71      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.53/0.71      inference('sup-', [status(thm)], ['64', '67'])).
% 0.53/0.71  thf('87', plain,
% 0.53/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.71         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.53/0.71          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.53/0.71  thf('88', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.53/0.71      inference('sup-', [status(thm)], ['86', '87'])).
% 0.53/0.71  thf('89', plain,
% 0.53/0.71      (((((sk_A) = (k1_xboole_0))
% 0.53/0.71         | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71         | ((sk_C) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)))),
% 0.53/0.71      inference('demod', [status(thm)], ['85', '88'])).
% 0.53/0.71  thf('90', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.53/0.71  thf('91', plain,
% 0.53/0.71      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.71         | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71         | ((sk_A) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['89', '90'])).
% 0.53/0.71  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('93', plain,
% 0.53/0.71      (((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)))),
% 0.53/0.71      inference('demod', [status(thm)], ['91', '92'])).
% 0.53/0.71  thf('94', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.53/0.71      inference('clc', [status(thm)], ['63', '72'])).
% 0.53/0.71  thf('95', plain,
% 0.53/0.71      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['93', '94'])).
% 0.53/0.71  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('97', plain,
% 0.53/0.71      ((((sk_A) = (k1_xboole_0)))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)))),
% 0.53/0.71      inference('demod', [status(thm)], ['95', '96'])).
% 0.53/0.71  thf('98', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.53/0.71      inference('clc', [status(thm)], ['16', '32'])).
% 0.53/0.71  thf('99', plain,
% 0.53/0.71      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.53/0.71         <= (~
% 0.53/0.71             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['97', '98'])).
% 0.53/0.71  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('101', plain,
% 0.53/0.71      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D))),
% 0.53/0.71      inference('demod', [status(thm)], ['99', '100'])).
% 0.53/0.71  thf('102', plain,
% 0.53/0.71      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_E)) | 
% 0.53/0.71       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_D)) | 
% 0.53/0.71       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_F))),
% 0.53/0.71      inference('split', [status(esa)], ['37'])).
% 0.53/0.71  thf('103', plain,
% 0.53/0.71      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_E))),
% 0.53/0.71      inference('sat_resolution*', [status(thm)], ['80', '101', '102'])).
% 0.53/0.71  thf('104', plain,
% 0.53/0.71      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_G) @ sk_E)),
% 0.53/0.71      inference('simpl_trail', [status(thm)], ['38', '103'])).
% 0.53/0.71  thf('105', plain,
% 0.53/0.71      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.53/0.71        | ((sk_A) = (k1_xboole_0))
% 0.53/0.71        | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71        | ((sk_C) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['36', '104'])).
% 0.53/0.71  thf('106', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.53/0.71      inference('sup-', [status(thm)], ['68', '69'])).
% 0.53/0.71  thf('107', plain,
% 0.53/0.71      ((((sk_A) = (k1_xboole_0))
% 0.53/0.71        | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71        | ((sk_C) = (k1_xboole_0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['105', '106'])).
% 0.53/0.71  thf('108', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.53/0.71  thf('109', plain,
% 0.53/0.71      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.71        | ((sk_B_2) = (k1_xboole_0))
% 0.53/0.71        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['107', '108'])).
% 0.53/0.71  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('111', plain, ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['109', '110'])).
% 0.53/0.71  thf('112', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.53/0.71      inference('clc', [status(thm)], ['63', '72'])).
% 0.53/0.71  thf('113', plain,
% 0.53/0.71      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['111', '112'])).
% 0.53/0.71  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('115', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.71      inference('demod', [status(thm)], ['113', '114'])).
% 0.53/0.71  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('117', plain, ($false),
% 0.53/0.71      inference('demod', [status(thm)], ['33', '115', '116'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
