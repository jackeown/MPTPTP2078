%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r7zcenp29h

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:35 EST 2020

% Result     : Theorem 15.31s
% Output     : Refutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 299 expanded)
%              Number of leaves         :   28 ( 100 expanded)
%              Depth                    :   27
%              Number of atoms          : 1623 (4454 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t26_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_orders_2 @ A @ B @ C )
                      & ( r1_orders_2 @ A @ C @ D ) )
                   => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r1_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_orders_2])).

thf('0',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d5_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v4_orders_2 @ A )
      <=> ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X18: $i] :
      ( ~ ( v4_orders_2 @ X18 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d8_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r8_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i,E: $i] :
              ( ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) )
             => ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X13 ) @ ( sk_E @ X12 @ X13 ) ) @ X13 )
      | ( r8_relat_2 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X12 @ X13 ) @ ( sk_D @ X12 @ X13 ) ) @ X13 )
      | ( r8_relat_2 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X13 ) @ ( sk_E @ X12 @ X13 ) ) @ X13 )
      | ( r8_relat_2 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X12 @ X13 ) @ ( sk_D @ X12 @ X13 ) ) @ X13 )
      | ( r8_relat_2 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r8_relat_2 @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X13 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X3 )
      | ~ ( r8_relat_2 @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r8_relat_2 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_E @ X1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ~ ( r8_relat_2 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r8_relat_2 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_E @ X1 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X12 @ X13 ) @ ( sk_E @ X12 @ X13 ) ) @ X13 )
      | ( r8_relat_2 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('76',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('77',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r8_relat_2 @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X13 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ~ ( r2_hidden @ sk_C_1 @ X1 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','82'])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','86'])).

thf('88',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('90',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('94',plain,(
    r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('97',plain,(
    r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['87','94','97'])).

thf('99',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('100',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r7zcenp29h
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.31/15.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.31/15.55  % Solved by: fo/fo7.sh
% 15.31/15.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.31/15.55  % done 2896 iterations in 15.088s
% 15.31/15.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.31/15.55  % SZS output start Refutation
% 15.31/15.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 15.31/15.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 15.31/15.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 15.31/15.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 15.31/15.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.31/15.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 15.31/15.55  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 15.31/15.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.31/15.55  thf(sk_A_type, type, sk_A: $i).
% 15.31/15.55  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 15.31/15.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 15.31/15.55  thf(sk_B_type, type, sk_B: $i).
% 15.31/15.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 15.31/15.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 15.31/15.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 15.31/15.55  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 15.31/15.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.31/15.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.31/15.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.31/15.55  thf(t26_orders_2, conjecture,
% 15.31/15.55    (![A:$i]:
% 15.31/15.55     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 15.31/15.55       ( ![B:$i]:
% 15.31/15.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 15.31/15.55           ( ![C:$i]:
% 15.31/15.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 15.31/15.55               ( ![D:$i]:
% 15.31/15.55                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 15.31/15.55                   ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 15.31/15.55                       ( r1_orders_2 @ A @ C @ D ) ) =>
% 15.31/15.55                     ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 15.31/15.55  thf(zf_stmt_0, negated_conjecture,
% 15.31/15.55    (~( ![A:$i]:
% 15.31/15.55        ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 15.31/15.55          ( ![B:$i]:
% 15.31/15.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 15.31/15.55              ( ![C:$i]:
% 15.31/15.55                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 15.31/15.55                  ( ![D:$i]:
% 15.31/15.55                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 15.31/15.55                      ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 15.31/15.55                          ( r1_orders_2 @ A @ C @ D ) ) =>
% 15.31/15.55                        ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 15.31/15.55    inference('cnf.neg', [status(esa)], [t26_orders_2])).
% 15.31/15.55  thf('0', plain, (~ (r1_orders_2 @ sk_A @ sk_B @ sk_D_1)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf(d9_orders_2, axiom,
% 15.31/15.55    (![A:$i]:
% 15.31/15.55     ( ( l1_orders_2 @ A ) =>
% 15.31/15.55       ( ![B:$i]:
% 15.31/15.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 15.31/15.55           ( ![C:$i]:
% 15.31/15.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 15.31/15.55               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 15.31/15.55                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 15.31/15.55  thf('3', plain,
% 15.31/15.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 15.31/15.55         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 15.31/15.55          | ~ (r1_orders_2 @ X20 @ X19 @ X21)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 15.31/15.55          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 15.31/15.55          | ~ (l1_orders_2 @ X20))),
% 15.31/15.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 15.31/15.55  thf('4', plain,
% 15.31/15.55      (![X0 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ sk_A)
% 15.31/15.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 15.31/15.55      inference('sup-', [status(thm)], ['2', '3'])).
% 15.31/15.55  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('6', plain,
% 15.31/15.55      (![X0 : $i]:
% 15.31/15.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 15.31/15.55      inference('demod', [status(thm)], ['4', '5'])).
% 15.31/15.55  thf('7', plain,
% 15.31/15.55      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 15.31/15.55        | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['1', '6'])).
% 15.31/15.55  thf('8', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('9', plain,
% 15.31/15.55      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 15.31/15.55      inference('demod', [status(thm)], ['7', '8'])).
% 15.31/15.55  thf(dt_u1_orders_2, axiom,
% 15.31/15.55    (![A:$i]:
% 15.31/15.55     ( ( l1_orders_2 @ A ) =>
% 15.31/15.55       ( m1_subset_1 @
% 15.31/15.55         ( u1_orders_2 @ A ) @ 
% 15.31/15.55         ( k1_zfmisc_1 @
% 15.31/15.55           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 15.31/15.55  thf('10', plain,
% 15.31/15.55      (![X22 : $i]:
% 15.31/15.55         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 15.31/15.55           (k1_zfmisc_1 @ 
% 15.31/15.55            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 15.31/15.55          | ~ (l1_orders_2 @ X22))),
% 15.31/15.55      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 15.31/15.55  thf(l3_subset_1, axiom,
% 15.31/15.55    (![A:$i,B:$i]:
% 15.31/15.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 15.31/15.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 15.31/15.55  thf('11', plain,
% 15.31/15.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 15.31/15.55         (~ (r2_hidden @ X5 @ X6)
% 15.31/15.55          | (r2_hidden @ X5 @ X7)
% 15.31/15.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 15.31/15.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 15.31/15.55  thf('12', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r2_hidden @ X1 @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['10', '11'])).
% 15.31/15.55  thf('13', plain,
% 15.31/15.55      (((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 15.31/15.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 15.31/15.55        | ~ (l1_orders_2 @ sk_A))),
% 15.31/15.55      inference('sup-', [status(thm)], ['9', '12'])).
% 15.31/15.55  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('15', plain,
% 15.31/15.55      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 15.31/15.55        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 15.31/15.55      inference('demod', [status(thm)], ['13', '14'])).
% 15.31/15.55  thf(l54_zfmisc_1, axiom,
% 15.31/15.55    (![A:$i,B:$i,C:$i,D:$i]:
% 15.31/15.55     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 15.31/15.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 15.31/15.55  thf('16', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.31/15.55         ((r2_hidden @ X2 @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.31/15.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.31/15.55  thf('17', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('sup-', [status(thm)], ['15', '16'])).
% 15.31/15.55  thf('18', plain,
% 15.31/15.55      (![X22 : $i]:
% 15.31/15.55         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 15.31/15.55           (k1_zfmisc_1 @ 
% 15.31/15.55            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 15.31/15.55          | ~ (l1_orders_2 @ X22))),
% 15.31/15.55      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 15.31/15.55  thf(cc2_relat_1, axiom,
% 15.31/15.55    (![A:$i]:
% 15.31/15.55     ( ( v1_relat_1 @ A ) =>
% 15.31/15.55       ( ![B:$i]:
% 15.31/15.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 15.31/15.55  thf('19', plain,
% 15.31/15.55      (![X8 : $i, X9 : $i]:
% 15.31/15.55         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 15.31/15.55          | (v1_relat_1 @ X8)
% 15.31/15.55          | ~ (v1_relat_1 @ X9))),
% 15.31/15.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 15.31/15.55  thf('20', plain,
% 15.31/15.55      (![X0 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v1_relat_1 @ 
% 15.31/15.55               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['18', '19'])).
% 15.31/15.55  thf(fc6_relat_1, axiom,
% 15.31/15.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 15.31/15.55  thf('21', plain,
% 15.31/15.55      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 15.31/15.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 15.31/15.55  thf('22', plain,
% 15.31/15.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('demod', [status(thm)], ['20', '21'])).
% 15.31/15.55  thf('23', plain,
% 15.31/15.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('demod', [status(thm)], ['20', '21'])).
% 15.31/15.55  thf(d5_orders_2, axiom,
% 15.31/15.55    (![A:$i]:
% 15.31/15.55     ( ( l1_orders_2 @ A ) =>
% 15.31/15.55       ( ( v4_orders_2 @ A ) <=>
% 15.31/15.55         ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 15.31/15.55  thf('24', plain,
% 15.31/15.55      (![X18 : $i]:
% 15.31/15.55         (~ (v4_orders_2 @ X18)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X18) @ (u1_struct_0 @ X18))
% 15.31/15.55          | ~ (l1_orders_2 @ X18))),
% 15.31/15.55      inference('cnf', [status(esa)], [d5_orders_2])).
% 15.31/15.55  thf('25', plain,
% 15.31/15.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('demod', [status(thm)], ['20', '21'])).
% 15.31/15.55  thf(d8_relat_2, axiom,
% 15.31/15.55    (![A:$i]:
% 15.31/15.55     ( ( v1_relat_1 @ A ) =>
% 15.31/15.55       ( ![B:$i]:
% 15.31/15.55         ( ( r8_relat_2 @ A @ B ) <=>
% 15.31/15.55           ( ![C:$i,D:$i,E:$i]:
% 15.31/15.55             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 15.31/15.55                 ( r2_hidden @ E @ B ) & 
% 15.31/15.55                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 15.31/15.55                 ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) =>
% 15.31/15.55               ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) ) ))).
% 15.31/15.55  thf('26', plain,
% 15.31/15.55      (![X12 : $i, X13 : $i]:
% 15.31/15.55         ((r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X13) @ (sk_E @ X12 @ X13)) @ 
% 15.31/15.55           X13)
% 15.31/15.55          | (r8_relat_2 @ X13 @ X12)
% 15.31/15.55          | ~ (v1_relat_1 @ X13))),
% 15.31/15.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.31/15.55  thf('27', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r2_hidden @ X1 @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['10', '11'])).
% 15.31/15.55  thf('28', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_D @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('sup-', [status(thm)], ['26', '27'])).
% 15.31/15.55  thf('29', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_D @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.31/15.55      inference('sup-', [status(thm)], ['25', '28'])).
% 15.31/15.55  thf('30', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_D @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['29'])).
% 15.31/15.55  thf('31', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.31/15.55         ((r2_hidden @ X2 @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.31/15.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.31/15.55  thf('32', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ (u1_struct_0 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['30', '31'])).
% 15.31/15.55  thf('33', plain,
% 15.31/15.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('demod', [status(thm)], ['20', '21'])).
% 15.31/15.55  thf('34', plain,
% 15.31/15.55      (![X12 : $i, X13 : $i]:
% 15.31/15.55         ((r2_hidden @ (k4_tarski @ (sk_C @ X12 @ X13) @ (sk_D @ X12 @ X13)) @ 
% 15.31/15.55           X13)
% 15.31/15.55          | (r8_relat_2 @ X13 @ X12)
% 15.31/15.55          | ~ (v1_relat_1 @ X13))),
% 15.31/15.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.31/15.55  thf('35', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r2_hidden @ X1 @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['10', '11'])).
% 15.31/15.55  thf('36', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_D @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('sup-', [status(thm)], ['34', '35'])).
% 15.31/15.55  thf('37', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_D @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.31/15.55      inference('sup-', [status(thm)], ['33', '36'])).
% 15.31/15.55  thf('38', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_D @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['37'])).
% 15.31/15.55  thf('39', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.31/15.55         ((r2_hidden @ X0 @ X1)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.31/15.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.31/15.55  thf('40', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ (u1_struct_0 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['38', '39'])).
% 15.31/15.55  thf('41', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_D @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['37'])).
% 15.31/15.55  thf('42', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.31/15.55         ((r2_hidden @ X2 @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.31/15.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.31/15.55  thf('43', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ (sk_D @ X1 @ (u1_orders_2 @ X0)) @ (u1_struct_0 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['41', '42'])).
% 15.31/15.55  thf('44', plain,
% 15.31/15.55      (![X12 : $i, X13 : $i]:
% 15.31/15.55         ((r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X13) @ (sk_E @ X12 @ X13)) @ 
% 15.31/15.55           X13)
% 15.31/15.55          | (r8_relat_2 @ X13 @ X12)
% 15.31/15.55          | ~ (v1_relat_1 @ X13))),
% 15.31/15.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.31/15.55  thf('45', plain,
% 15.31/15.55      (![X12 : $i, X13 : $i]:
% 15.31/15.55         ((r2_hidden @ (k4_tarski @ (sk_C @ X12 @ X13) @ (sk_D @ X12 @ X13)) @ 
% 15.31/15.55           X13)
% 15.31/15.55          | (r8_relat_2 @ X13 @ X12)
% 15.31/15.55          | ~ (v1_relat_1 @ X13))),
% 15.31/15.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.31/15.55  thf('46', plain,
% 15.31/15.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 15.31/15.55         (~ (r8_relat_2 @ X13 @ X14)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X13)
% 15.31/15.55          | ~ (r2_hidden @ X16 @ X14)
% 15.31/15.55          | ~ (r2_hidden @ X15 @ X14)
% 15.31/15.55          | ~ (r2_hidden @ X17 @ X14)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X13)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X13)
% 15.31/15.55          | ~ (v1_relat_1 @ X13))),
% 15.31/15.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.31/15.55  thf('47', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.31/15.55         (~ (v1_relat_1 @ X0)
% 15.31/15.55          | (r8_relat_2 @ X0 @ X1)
% 15.31/15.55          | ~ (v1_relat_1 @ X0)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ X2) @ X0)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ X2) @ X0)
% 15.31/15.55          | ~ (r2_hidden @ X2 @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X3)
% 15.31/15.55          | ~ (r8_relat_2 @ X0 @ X3))),
% 15.31/15.55      inference('sup-', [status(thm)], ['45', '46'])).
% 15.31/15.55  thf('48', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.31/15.55         (~ (r8_relat_2 @ X0 @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X3)
% 15.31/15.55          | ~ (r2_hidden @ X2 @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ X2) @ X0)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ X2) @ X0)
% 15.31/15.55          | (r8_relat_2 @ X0 @ X1)
% 15.31/15.55          | ~ (v1_relat_1 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['47'])).
% 15.31/15.55  thf('49', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.55         (~ (v1_relat_1 @ X0)
% 15.31/15.55          | (r8_relat_2 @ X0 @ X1)
% 15.31/15.55          | ~ (v1_relat_1 @ X0)
% 15.31/15.55          | (r8_relat_2 @ X0 @ X1)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_E @ X1 @ X0)) @ X0)
% 15.31/15.55          | ~ (r2_hidden @ (sk_E @ X1 @ X0) @ X2)
% 15.31/15.55          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 15.31/15.55          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 15.31/15.55          | ~ (r8_relat_2 @ X0 @ X2))),
% 15.31/15.55      inference('sup-', [status(thm)], ['44', '48'])).
% 15.31/15.55  thf('50', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.55         (~ (r8_relat_2 @ X0 @ X2)
% 15.31/15.55          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 15.31/15.55          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 15.31/15.55          | ~ (r2_hidden @ (sk_E @ X1 @ X0) @ X2)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_E @ X1 @ X0)) @ X0)
% 15.31/15.55          | (r8_relat_2 @ X0 @ X1)
% 15.31/15.55          | ~ (v1_relat_1 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['49'])).
% 15.31/15.55  thf('51', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55               (u1_struct_0 @ X0))
% 15.31/15.55          | ~ (r2_hidden @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55               (u1_struct_0 @ X0))
% 15.31/15.55          | ~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['43', '50'])).
% 15.31/15.55  thf('52', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0))
% 15.31/15.55          | ~ (r2_hidden @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55               (u1_struct_0 @ X0))
% 15.31/15.55          | ~ (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55               (u1_struct_0 @ X0))
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.31/15.55      inference('simplify', [status(thm)], ['51'])).
% 15.31/15.55  thf('53', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55               (u1_struct_0 @ X0))
% 15.31/15.55          | ~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['40', '52'])).
% 15.31/15.55  thf('54', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0))
% 15.31/15.55          | ~ (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55               (u1_struct_0 @ X0))
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.31/15.55      inference('simplify', [status(thm)], ['53'])).
% 15.31/15.55  thf('55', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['32', '54'])).
% 15.31/15.55  thf('56', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0))
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.31/15.55      inference('simplify', [status(thm)], ['55'])).
% 15.31/15.55  thf('57', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v4_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['24', '56'])).
% 15.31/15.55  thf('58', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r2_hidden @ 
% 15.31/15.55           (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55            (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55           (u1_orders_2 @ X0))
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (v4_orders_2 @ X0)
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['57'])).
% 15.31/15.55  thf('59', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v4_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55             (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['23', '58'])).
% 15.31/15.55  thf('60', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r2_hidden @ 
% 15.31/15.55           (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.31/15.55            (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.31/15.55           (u1_orders_2 @ X0))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (v4_orders_2 @ X0)
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['59'])).
% 15.31/15.55  thf('61', plain,
% 15.31/15.55      (![X12 : $i, X13 : $i]:
% 15.31/15.55         (~ (r2_hidden @ 
% 15.31/15.55             (k4_tarski @ (sk_C @ X12 @ X13) @ (sk_E @ X12 @ X13)) @ X13)
% 15.31/15.55          | (r8_relat_2 @ X13 @ X12)
% 15.31/15.55          | ~ (v1_relat_1 @ X13))),
% 15.31/15.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.31/15.55  thf('62', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v4_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.31/15.55      inference('sup-', [status(thm)], ['60', '61'])).
% 15.31/15.55  thf('63', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (v4_orders_2 @ X0)
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['62'])).
% 15.31/15.55  thf('64', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (l1_orders_2 @ X0)
% 15.31/15.55          | ~ (v4_orders_2 @ X0)
% 15.31/15.55          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.31/15.55      inference('sup-', [status(thm)], ['22', '63'])).
% 15.31/15.55  thf('65', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.31/15.55          | ~ (v4_orders_2 @ X0)
% 15.31/15.55          | ~ (l1_orders_2 @ X0))),
% 15.31/15.55      inference('simplify', [status(thm)], ['64'])).
% 15.31/15.55  thf('66', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('67', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('68', plain,
% 15.31/15.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 15.31/15.55         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 15.31/15.55          | ~ (r1_orders_2 @ X20 @ X19 @ X21)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 15.31/15.55          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 15.31/15.55          | ~ (l1_orders_2 @ X20))),
% 15.31/15.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 15.31/15.55  thf('69', plain,
% 15.31/15.55      (![X0 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ sk_A)
% 15.31/15.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 15.31/15.55      inference('sup-', [status(thm)], ['67', '68'])).
% 15.31/15.55  thf('70', plain, ((l1_orders_2 @ sk_A)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('71', plain,
% 15.31/15.55      (![X0 : $i]:
% 15.31/15.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 15.31/15.55      inference('demod', [status(thm)], ['69', '70'])).
% 15.31/15.55  thf('72', plain,
% 15.31/15.55      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1)
% 15.31/15.55        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['66', '71'])).
% 15.31/15.55  thf('73', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('74', plain,
% 15.31/15.55      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 15.31/15.55      inference('demod', [status(thm)], ['72', '73'])).
% 15.31/15.55  thf('75', plain,
% 15.31/15.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('demod', [status(thm)], ['20', '21'])).
% 15.31/15.55  thf('76', plain,
% 15.31/15.55      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 15.31/15.55      inference('demod', [status(thm)], ['7', '8'])).
% 15.31/15.55  thf('77', plain,
% 15.31/15.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 15.31/15.55         (~ (r8_relat_2 @ X13 @ X14)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X13)
% 15.31/15.55          | ~ (r2_hidden @ X16 @ X14)
% 15.31/15.55          | ~ (r2_hidden @ X15 @ X14)
% 15.31/15.55          | ~ (r2_hidden @ X17 @ X14)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X13)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X13)
% 15.31/15.55          | ~ (v1_relat_1 @ X13))),
% 15.31/15.55      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.31/15.55  thf('78', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | ~ (r2_hidden @ X0 @ X1)
% 15.31/15.55          | ~ (r2_hidden @ sk_B @ X1)
% 15.31/15.55          | ~ (r2_hidden @ sk_C_1 @ X1)
% 15.31/15.55          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X1))),
% 15.31/15.55      inference('sup-', [status(thm)], ['76', '77'])).
% 15.31/15.55  thf('79', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ sk_A)
% 15.31/15.55          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_B @ X0)
% 15.31/15.55          | ~ (r2_hidden @ X1 @ X0)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X1) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_B @ X1) @ (u1_orders_2 @ sk_A)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['75', '78'])).
% 15.31/15.55  thf('80', plain, ((l1_orders_2 @ sk_A)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('81', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_B @ X0)
% 15.31/15.55          | ~ (r2_hidden @ X1 @ X0)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X1) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_B @ X1) @ (u1_orders_2 @ sk_A)))),
% 15.31/15.55      inference('demod', [status(thm)], ['79', '80'])).
% 15.31/15.55  thf('82', plain,
% 15.31/15.55      (![X0 : $i]:
% 15.31/15.55         ((r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 15.31/15.55          | ~ (r2_hidden @ sk_D_1 @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_B @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 15.31/15.55          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 15.31/15.55      inference('sup-', [status(thm)], ['74', '81'])).
% 15.31/15.55  thf('83', plain,
% 15.31/15.55      (![X0 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ sk_A)
% 15.31/15.55          | ~ (v4_orders_2 @ sk_A)
% 15.31/15.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_B @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_D_1 @ X0)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['65', '82'])).
% 15.31/15.55  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('85', plain, ((v4_orders_2 @ sk_A)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('86', plain,
% 15.31/15.55      (![X0 : $i]:
% 15.31/15.55         (~ (r2_hidden @ sk_C_1 @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_B @ X0)
% 15.31/15.55          | ~ (r2_hidden @ sk_D_1 @ X0)
% 15.31/15.55          | (r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 15.31/15.55      inference('demod', [status(thm)], ['83', '84', '85'])).
% 15.31/15.55  thf('87', plain,
% 15.31/15.55      (((r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 15.31/15.55        | ~ (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 15.31/15.55        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['17', '86'])).
% 15.31/15.55  thf('88', plain,
% 15.31/15.55      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 15.31/15.55      inference('demod', [status(thm)], ['72', '73'])).
% 15.31/15.55  thf('89', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i]:
% 15.31/15.55         (~ (l1_orders_2 @ X0)
% 15.31/15.55          | (r2_hidden @ X1 @ 
% 15.31/15.55             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.31/15.55          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['10', '11'])).
% 15.31/15.55  thf('90', plain,
% 15.31/15.55      (((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ 
% 15.31/15.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 15.31/15.55        | ~ (l1_orders_2 @ sk_A))),
% 15.31/15.55      inference('sup-', [status(thm)], ['88', '89'])).
% 15.31/15.55  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('92', plain,
% 15.31/15.55      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ 
% 15.31/15.55        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 15.31/15.55      inference('demod', [status(thm)], ['90', '91'])).
% 15.31/15.55  thf('93', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.31/15.55         ((r2_hidden @ X2 @ X3)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.31/15.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.31/15.55  thf('94', plain, ((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('sup-', [status(thm)], ['92', '93'])).
% 15.31/15.55  thf('95', plain,
% 15.31/15.55      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 15.31/15.55        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 15.31/15.55      inference('demod', [status(thm)], ['13', '14'])).
% 15.31/15.55  thf('96', plain,
% 15.31/15.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.31/15.55         ((r2_hidden @ X0 @ X1)
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.31/15.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.31/15.55  thf('97', plain, ((r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('sup-', [status(thm)], ['95', '96'])).
% 15.31/15.55  thf('98', plain,
% 15.31/15.55      ((r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 15.31/15.55      inference('demod', [status(thm)], ['87', '94', '97'])).
% 15.31/15.55  thf('99', plain,
% 15.31/15.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 15.31/15.55         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 15.31/15.55          | ~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 15.31/15.55          | (r1_orders_2 @ X20 @ X19 @ X21)
% 15.31/15.55          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 15.31/15.55          | ~ (l1_orders_2 @ X20))),
% 15.31/15.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 15.31/15.55  thf('100', plain,
% 15.31/15.55      ((~ (l1_orders_2 @ sk_A)
% 15.31/15.55        | ~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 15.31/15.55        | (r1_orders_2 @ sk_A @ sk_B @ sk_D_1)
% 15.31/15.55        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 15.31/15.55      inference('sup-', [status(thm)], ['98', '99'])).
% 15.31/15.55  thf('101', plain, ((l1_orders_2 @ sk_A)),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('102', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('103', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 15.31/15.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.55  thf('104', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_D_1)),
% 15.31/15.55      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 15.31/15.55  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 15.31/15.55  
% 15.31/15.55  % SZS output end Refutation
% 15.31/15.55  
% 15.31/15.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
