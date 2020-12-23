%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LZ06nmuOsc

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:35 EST 2020

% Result     : Theorem 15.06s
% Output     : Refutation 15.10s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 281 expanded)
%              Number of leaves         :   27 (  94 expanded)
%              Depth                    :   27
%              Number of atoms          : 1604 (4340 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
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
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
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
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d5_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v4_orders_2 @ A )
      <=> ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( ~ ( v4_orders_2 @ X17 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X12 ) @ ( sk_E @ X11 @ X12 ) ) @ X12 )
      | ( r8_relat_2 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X11 @ X12 ) @ ( sk_D @ X11 @ X12 ) ) @ X12 )
      | ( r8_relat_2 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X12 ) @ ( sk_E @ X11 @ X12 ) ) @ X12 )
      | ( r8_relat_2 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X11 @ X12 ) @ ( sk_D @ X11 @ X12 ) ) @ X12 )
      | ( r8_relat_2 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r8_relat_2 @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X12 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('45',plain,(
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
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r8_relat_2 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
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
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r8_relat_2 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_E @ X1 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
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
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X11 @ X12 ) @ ( sk_E @ X11 @ X12 ) ) @ X12 )
      | ( r8_relat_2 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('74',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('75',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r8_relat_2 @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X12 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ~ ( r2_hidden @ sk_C_1 @ X1 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','80'])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','84'])).

thf('86',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('88',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('92',plain,(
    r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('95',plain,(
    r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['85','92','95'])).

thf('97',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('98',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LZ06nmuOsc
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:22:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 15.06/15.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.06/15.27  % Solved by: fo/fo7.sh
% 15.06/15.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.06/15.27  % done 2702 iterations in 14.812s
% 15.06/15.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.06/15.27  % SZS output start Refutation
% 15.06/15.27  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 15.06/15.27  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 15.06/15.27  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 15.06/15.27  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 15.06/15.27  thf(sk_B_type, type, sk_B: $i).
% 15.06/15.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 15.06/15.27  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 15.06/15.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.06/15.27  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 15.06/15.27  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 15.06/15.27  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 15.06/15.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.06/15.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 15.06/15.27  thf(sk_D_1_type, type, sk_D_1: $i).
% 15.06/15.27  thf(sk_A_type, type, sk_A: $i).
% 15.06/15.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.06/15.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.06/15.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.06/15.27  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 15.06/15.27  thf(t26_orders_2, conjecture,
% 15.06/15.27    (![A:$i]:
% 15.06/15.27     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 15.06/15.27       ( ![B:$i]:
% 15.06/15.27         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 15.06/15.27           ( ![C:$i]:
% 15.06/15.27             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 15.06/15.27               ( ![D:$i]:
% 15.06/15.27                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 15.06/15.27                   ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 15.06/15.27                       ( r1_orders_2 @ A @ C @ D ) ) =>
% 15.06/15.27                     ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 15.06/15.27  thf(zf_stmt_0, negated_conjecture,
% 15.06/15.27    (~( ![A:$i]:
% 15.06/15.27        ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 15.06/15.27          ( ![B:$i]:
% 15.06/15.27            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 15.06/15.27              ( ![C:$i]:
% 15.06/15.27                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 15.06/15.27                  ( ![D:$i]:
% 15.06/15.27                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 15.06/15.27                      ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 15.06/15.27                          ( r1_orders_2 @ A @ C @ D ) ) =>
% 15.06/15.27                        ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 15.06/15.27    inference('cnf.neg', [status(esa)], [t26_orders_2])).
% 15.06/15.27  thf('0', plain, (~ (r1_orders_2 @ sk_A @ sk_B @ sk_D_1)),
% 15.06/15.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.06/15.27  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 15.06/15.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.06/15.27  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 15.06/15.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.06/15.27  thf(d9_orders_2, axiom,
% 15.06/15.27    (![A:$i]:
% 15.06/15.27     ( ( l1_orders_2 @ A ) =>
% 15.06/15.27       ( ![B:$i]:
% 15.06/15.27         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 15.06/15.27           ( ![C:$i]:
% 15.06/15.27             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 15.06/15.27               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 15.06/15.27                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 15.06/15.27  thf('3', plain,
% 15.06/15.27      (![X18 : $i, X19 : $i, X20 : $i]:
% 15.06/15.27         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 15.06/15.27          | ~ (r1_orders_2 @ X19 @ X18 @ X20)
% 15.06/15.27          | (r2_hidden @ (k4_tarski @ X18 @ X20) @ (u1_orders_2 @ X19))
% 15.06/15.27          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 15.06/15.27          | ~ (l1_orders_2 @ X19))),
% 15.06/15.27      inference('cnf', [status(esa)], [d9_orders_2])).
% 15.06/15.27  thf('4', plain,
% 15.06/15.27      (![X0 : $i]:
% 15.06/15.27         (~ (l1_orders_2 @ sk_A)
% 15.06/15.27          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 15.06/15.27          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 15.06/15.27          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 15.06/15.27      inference('sup-', [status(thm)], ['2', '3'])).
% 15.06/15.27  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 15.06/15.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.06/15.27  thf('6', plain,
% 15.06/15.27      (![X0 : $i]:
% 15.06/15.27         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 15.06/15.27          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 15.06/15.27          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 15.06/15.27      inference('demod', [status(thm)], ['4', '5'])).
% 15.06/15.27  thf('7', plain,
% 15.06/15.27      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 15.06/15.27        | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['1', '6'])).
% 15.06/15.27  thf('8', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 15.06/15.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.06/15.27  thf('9', plain,
% 15.06/15.27      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 15.06/15.27      inference('demod', [status(thm)], ['7', '8'])).
% 15.06/15.27  thf(dt_u1_orders_2, axiom,
% 15.06/15.27    (![A:$i]:
% 15.06/15.27     ( ( l1_orders_2 @ A ) =>
% 15.06/15.27       ( m1_subset_1 @
% 15.06/15.27         ( u1_orders_2 @ A ) @ 
% 15.06/15.27         ( k1_zfmisc_1 @
% 15.06/15.27           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 15.06/15.27  thf('10', plain,
% 15.06/15.27      (![X21 : $i]:
% 15.06/15.27         ((m1_subset_1 @ (u1_orders_2 @ X21) @ 
% 15.06/15.27           (k1_zfmisc_1 @ 
% 15.06/15.27            (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X21))))
% 15.06/15.27          | ~ (l1_orders_2 @ X21))),
% 15.06/15.27      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 15.06/15.27  thf(l3_subset_1, axiom,
% 15.06/15.27    (![A:$i,B:$i]:
% 15.06/15.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 15.06/15.27       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 15.06/15.27  thf('11', plain,
% 15.06/15.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 15.06/15.27         (~ (r2_hidden @ X5 @ X6)
% 15.06/15.27          | (r2_hidden @ X5 @ X7)
% 15.06/15.27          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 15.06/15.27      inference('cnf', [status(esa)], [l3_subset_1])).
% 15.06/15.27  thf('12', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (l1_orders_2 @ X0)
% 15.06/15.27          | (r2_hidden @ X1 @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['10', '11'])).
% 15.06/15.27  thf('13', plain,
% 15.06/15.27      (((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 15.06/15.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 15.06/15.27        | ~ (l1_orders_2 @ sk_A))),
% 15.06/15.27      inference('sup-', [status(thm)], ['9', '12'])).
% 15.06/15.27  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 15.06/15.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.06/15.27  thf('15', plain,
% 15.06/15.27      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 15.06/15.27        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 15.06/15.27      inference('demod', [status(thm)], ['13', '14'])).
% 15.06/15.27  thf(l54_zfmisc_1, axiom,
% 15.06/15.27    (![A:$i,B:$i,C:$i,D:$i]:
% 15.06/15.27     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 15.06/15.27       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 15.06/15.27  thf('16', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.06/15.27         ((r2_hidden @ X2 @ X3)
% 15.06/15.27          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.06/15.27      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.06/15.27  thf('17', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 15.06/15.27      inference('sup-', [status(thm)], ['15', '16'])).
% 15.06/15.27  thf('18', plain,
% 15.06/15.27      (![X21 : $i]:
% 15.06/15.27         ((m1_subset_1 @ (u1_orders_2 @ X21) @ 
% 15.06/15.27           (k1_zfmisc_1 @ 
% 15.06/15.27            (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X21))))
% 15.06/15.27          | ~ (l1_orders_2 @ X21))),
% 15.06/15.27      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 15.06/15.27  thf(cc1_relset_1, axiom,
% 15.06/15.27    (![A:$i,B:$i,C:$i]:
% 15.06/15.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.06/15.27       ( v1_relat_1 @ C ) ))).
% 15.06/15.27  thf('19', plain,
% 15.06/15.27      (![X8 : $i, X9 : $i, X10 : $i]:
% 15.06/15.27         ((v1_relat_1 @ X8)
% 15.06/15.27          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 15.06/15.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.06/15.27  thf('20', plain,
% 15.06/15.27      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['18', '19'])).
% 15.06/15.27  thf('21', plain,
% 15.06/15.27      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['18', '19'])).
% 15.06/15.27  thf(d5_orders_2, axiom,
% 15.06/15.27    (![A:$i]:
% 15.06/15.27     ( ( l1_orders_2 @ A ) =>
% 15.06/15.27       ( ( v4_orders_2 @ A ) <=>
% 15.06/15.27         ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 15.06/15.27  thf('22', plain,
% 15.06/15.27      (![X17 : $i]:
% 15.06/15.27         (~ (v4_orders_2 @ X17)
% 15.06/15.27          | (r8_relat_2 @ (u1_orders_2 @ X17) @ (u1_struct_0 @ X17))
% 15.06/15.27          | ~ (l1_orders_2 @ X17))),
% 15.06/15.27      inference('cnf', [status(esa)], [d5_orders_2])).
% 15.06/15.27  thf('23', plain,
% 15.06/15.27      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['18', '19'])).
% 15.06/15.27  thf(d8_relat_2, axiom,
% 15.06/15.27    (![A:$i]:
% 15.06/15.27     ( ( v1_relat_1 @ A ) =>
% 15.06/15.27       ( ![B:$i]:
% 15.06/15.27         ( ( r8_relat_2 @ A @ B ) <=>
% 15.06/15.27           ( ![C:$i,D:$i,E:$i]:
% 15.06/15.27             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 15.06/15.27                 ( r2_hidden @ E @ B ) & 
% 15.06/15.27                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 15.06/15.27                 ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) =>
% 15.06/15.27               ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) ) ))).
% 15.06/15.27  thf('24', plain,
% 15.06/15.27      (![X11 : $i, X12 : $i]:
% 15.06/15.27         ((r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X12) @ (sk_E @ X11 @ X12)) @ 
% 15.06/15.27           X12)
% 15.06/15.27          | (r8_relat_2 @ X12 @ X11)
% 15.06/15.27          | ~ (v1_relat_1 @ X12))),
% 15.06/15.27      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.06/15.27  thf('25', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (l1_orders_2 @ X0)
% 15.06/15.27          | (r2_hidden @ X1 @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['10', '11'])).
% 15.06/15.27  thf('26', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.06/15.27          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.27          | (r2_hidden @ 
% 15.06/15.27             (k4_tarski @ (sk_D @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.27              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | ~ (l1_orders_2 @ X0))),
% 15.06/15.27      inference('sup-', [status(thm)], ['24', '25'])).
% 15.06/15.27  thf('27', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (l1_orders_2 @ X0)
% 15.06/15.27          | ~ (l1_orders_2 @ X0)
% 15.06/15.27          | (r2_hidden @ 
% 15.06/15.27             (k4_tarski @ (sk_D @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.27              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.06/15.27      inference('sup-', [status(thm)], ['23', '26'])).
% 15.06/15.27  thf('28', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.27          | (r2_hidden @ 
% 15.06/15.27             (k4_tarski @ (sk_D @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.27              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | ~ (l1_orders_2 @ X0))),
% 15.06/15.27      inference('simplify', [status(thm)], ['27'])).
% 15.06/15.27  thf('29', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.06/15.27         ((r2_hidden @ X2 @ X3)
% 15.06/15.27          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.06/15.27      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.06/15.27  thf('30', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (l1_orders_2 @ X0)
% 15.06/15.27          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.27          | (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ (u1_struct_0 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['28', '29'])).
% 15.06/15.27  thf('31', plain,
% 15.06/15.27      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['18', '19'])).
% 15.06/15.27  thf('32', plain,
% 15.06/15.27      (![X11 : $i, X12 : $i]:
% 15.06/15.27         ((r2_hidden @ (k4_tarski @ (sk_C @ X11 @ X12) @ (sk_D @ X11 @ X12)) @ 
% 15.06/15.27           X12)
% 15.06/15.27          | (r8_relat_2 @ X12 @ X11)
% 15.06/15.27          | ~ (v1_relat_1 @ X12))),
% 15.06/15.27      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.06/15.27  thf('33', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (l1_orders_2 @ X0)
% 15.06/15.27          | (r2_hidden @ X1 @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['10', '11'])).
% 15.06/15.27  thf('34', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.06/15.27          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.27          | (r2_hidden @ 
% 15.06/15.27             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.27              (sk_D @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | ~ (l1_orders_2 @ X0))),
% 15.06/15.27      inference('sup-', [status(thm)], ['32', '33'])).
% 15.06/15.27  thf('35', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (l1_orders_2 @ X0)
% 15.06/15.27          | ~ (l1_orders_2 @ X0)
% 15.06/15.27          | (r2_hidden @ 
% 15.06/15.27             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.27              (sk_D @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.06/15.27      inference('sup-', [status(thm)], ['31', '34'])).
% 15.06/15.27  thf('36', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.27          | (r2_hidden @ 
% 15.06/15.27             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.27              (sk_D @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.27          | ~ (l1_orders_2 @ X0))),
% 15.06/15.27      inference('simplify', [status(thm)], ['35'])).
% 15.06/15.27  thf('37', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.06/15.27         ((r2_hidden @ X0 @ X1)
% 15.06/15.27          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.06/15.27      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.06/15.27  thf('38', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         (~ (l1_orders_2 @ X0)
% 15.06/15.27          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.27          | (r2_hidden @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ (u1_struct_0 @ X0)))),
% 15.06/15.27      inference('sup-', [status(thm)], ['36', '37'])).
% 15.06/15.27  thf('39', plain,
% 15.06/15.27      (![X0 : $i, X1 : $i]:
% 15.06/15.27         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.27          | (r2_hidden @ 
% 15.06/15.27             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.27              (sk_D @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.27             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.06/15.28          | ~ (l1_orders_2 @ X0))),
% 15.06/15.28      inference('simplify', [status(thm)], ['35'])).
% 15.06/15.28  thf('40', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.06/15.28         ((r2_hidden @ X2 @ X3)
% 15.06/15.28          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.06/15.28      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.06/15.28  thf('41', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i]:
% 15.06/15.28         (~ (l1_orders_2 @ X0)
% 15.06/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.28          | (r2_hidden @ (sk_D @ X1 @ (u1_orders_2 @ X0)) @ (u1_struct_0 @ X0)))),
% 15.06/15.28      inference('sup-', [status(thm)], ['39', '40'])).
% 15.06/15.28  thf('42', plain,
% 15.06/15.28      (![X11 : $i, X12 : $i]:
% 15.06/15.28         ((r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X12) @ (sk_E @ X11 @ X12)) @ 
% 15.06/15.28           X12)
% 15.06/15.28          | (r8_relat_2 @ X12 @ X11)
% 15.06/15.28          | ~ (v1_relat_1 @ X12))),
% 15.06/15.28      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.06/15.28  thf('43', plain,
% 15.06/15.28      (![X11 : $i, X12 : $i]:
% 15.06/15.28         ((r2_hidden @ (k4_tarski @ (sk_C @ X11 @ X12) @ (sk_D @ X11 @ X12)) @ 
% 15.06/15.28           X12)
% 15.06/15.28          | (r8_relat_2 @ X12 @ X11)
% 15.06/15.28          | ~ (v1_relat_1 @ X12))),
% 15.06/15.28      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.06/15.28  thf('44', plain,
% 15.06/15.28      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 15.06/15.28         (~ (r8_relat_2 @ X12 @ X13)
% 15.06/15.28          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X12)
% 15.06/15.28          | ~ (r2_hidden @ X15 @ X13)
% 15.06/15.28          | ~ (r2_hidden @ X14 @ X13)
% 15.06/15.28          | ~ (r2_hidden @ X16 @ X13)
% 15.06/15.28          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X12)
% 15.06/15.28          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ X12)
% 15.06/15.28          | ~ (v1_relat_1 @ X12))),
% 15.06/15.28      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.06/15.28  thf('45', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.06/15.28         (~ (v1_relat_1 @ X0)
% 15.06/15.28          | (r8_relat_2 @ X0 @ X1)
% 15.06/15.28          | ~ (v1_relat_1 @ X0)
% 15.06/15.28          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ X2) @ X0)
% 15.06/15.28          | ~ (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ X2) @ X0)
% 15.06/15.28          | ~ (r2_hidden @ X2 @ X3)
% 15.06/15.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X3)
% 15.06/15.28          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X3)
% 15.06/15.28          | ~ (r8_relat_2 @ X0 @ X3))),
% 15.06/15.28      inference('sup-', [status(thm)], ['43', '44'])).
% 15.06/15.28  thf('46', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.06/15.28         (~ (r8_relat_2 @ X0 @ X3)
% 15.06/15.28          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X3)
% 15.06/15.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X3)
% 15.06/15.28          | ~ (r2_hidden @ X2 @ X3)
% 15.06/15.28          | ~ (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ X2) @ X0)
% 15.06/15.28          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ X2) @ X0)
% 15.06/15.28          | (r8_relat_2 @ X0 @ X1)
% 15.06/15.28          | ~ (v1_relat_1 @ X0))),
% 15.06/15.28      inference('simplify', [status(thm)], ['45'])).
% 15.06/15.28  thf('47', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.06/15.28         (~ (v1_relat_1 @ X0)
% 15.06/15.28          | (r8_relat_2 @ X0 @ X1)
% 15.06/15.28          | ~ (v1_relat_1 @ X0)
% 15.06/15.28          | (r8_relat_2 @ X0 @ X1)
% 15.06/15.28          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_E @ X1 @ X0)) @ X0)
% 15.06/15.28          | ~ (r2_hidden @ (sk_E @ X1 @ X0) @ X2)
% 15.06/15.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 15.06/15.28          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 15.06/15.28          | ~ (r8_relat_2 @ X0 @ X2))),
% 15.06/15.28      inference('sup-', [status(thm)], ['42', '46'])).
% 15.06/15.28  thf('48', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.06/15.28         (~ (r8_relat_2 @ X0 @ X2)
% 15.06/15.28          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 15.06/15.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 15.06/15.28          | ~ (r2_hidden @ (sk_E @ X1 @ X0) @ X2)
% 15.06/15.28          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_E @ X1 @ X0)) @ X0)
% 15.06/15.28          | (r8_relat_2 @ X0 @ X1)
% 15.06/15.28          | ~ (v1_relat_1 @ X0))),
% 15.06/15.28      inference('simplify', [status(thm)], ['47'])).
% 15.06/15.28  thf('49', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i]:
% 15.06/15.28         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.06/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.06/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.28          | (r2_hidden @ 
% 15.06/15.28             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.28             (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28               (u1_struct_0 @ X0))
% 15.06/15.28          | ~ (r2_hidden @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28               (u1_struct_0 @ X0))
% 15.06/15.28          | ~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0)))),
% 15.06/15.28      inference('sup-', [status(thm)], ['41', '48'])).
% 15.06/15.28  thf('50', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i]:
% 15.06/15.28         (~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0))
% 15.06/15.28          | ~ (r2_hidden @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28               (u1_struct_0 @ X0))
% 15.06/15.28          | ~ (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28               (u1_struct_0 @ X0))
% 15.06/15.28          | (r2_hidden @ 
% 15.06/15.28             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.28             (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.06/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.06/15.28      inference('simplify', [status(thm)], ['49'])).
% 15.06/15.28  thf('51', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i]:
% 15.06/15.28         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.06/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.06/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.06/15.28          | (r2_hidden @ 
% 15.06/15.28             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.28             (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28               (u1_struct_0 @ X0))
% 15.06/15.28          | ~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0)))),
% 15.06/15.28      inference('sup-', [status(thm)], ['38', '50'])).
% 15.06/15.28  thf('52', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i]:
% 15.06/15.28         (~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0))
% 15.06/15.28          | ~ (r2_hidden @ (sk_E @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28               (u1_struct_0 @ X0))
% 15.06/15.28          | (r2_hidden @ 
% 15.06/15.28             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.28             (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.06/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.06/15.28      inference('simplify', [status(thm)], ['51'])).
% 15.06/15.28  thf('53', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i]:
% 15.06/15.28         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.06/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.06/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.06/15.28          | (r2_hidden @ 
% 15.06/15.28             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.28             (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0)))),
% 15.06/15.28      inference('sup-', [status(thm)], ['30', '52'])).
% 15.06/15.28  thf('54', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i]:
% 15.06/15.28         (~ (r8_relat_2 @ (u1_orders_2 @ X0) @ (u1_struct_0 @ X0))
% 15.06/15.28          | (r2_hidden @ 
% 15.06/15.28             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.06/15.28              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.06/15.28             (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.06/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.06/15.28      inference('simplify', [status(thm)], ['53'])).
% 15.06/15.28  thf('55', plain,
% 15.06/15.28      (![X0 : $i, X1 : $i]:
% 15.06/15.28         (~ (l1_orders_2 @ X0)
% 15.06/15.28          | ~ (v4_orders_2 @ X0)
% 15.06/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.06/15.28          | ~ (l1_orders_2 @ X0)
% 15.10/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.10/15.28          | (r2_hidden @ 
% 15.10/15.28             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.10/15.28              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.10/15.28             (u1_orders_2 @ X0)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['22', '54'])).
% 15.10/15.28  thf('56', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         ((r2_hidden @ 
% 15.10/15.28           (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.10/15.28            (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.10/15.28           (u1_orders_2 @ X0))
% 15.10/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.10/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.10/15.28          | ~ (v4_orders_2 @ X0)
% 15.10/15.28          | ~ (l1_orders_2 @ X0))),
% 15.10/15.28      inference('simplify', [status(thm)], ['55'])).
% 15.10/15.28  thf('57', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         (~ (l1_orders_2 @ X0)
% 15.10/15.28          | ~ (l1_orders_2 @ X0)
% 15.10/15.28          | ~ (v4_orders_2 @ X0)
% 15.10/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.10/15.28          | (r2_hidden @ 
% 15.10/15.28             (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.10/15.28              (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.10/15.28             (u1_orders_2 @ X0)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['21', '56'])).
% 15.10/15.28  thf('58', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         ((r2_hidden @ 
% 15.10/15.28           (k4_tarski @ (sk_C @ X1 @ (u1_orders_2 @ X0)) @ 
% 15.10/15.28            (sk_E @ X1 @ (u1_orders_2 @ X0))) @ 
% 15.10/15.28           (u1_orders_2 @ X0))
% 15.10/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.10/15.28          | ~ (v4_orders_2 @ X0)
% 15.10/15.28          | ~ (l1_orders_2 @ X0))),
% 15.10/15.28      inference('simplify', [status(thm)], ['57'])).
% 15.10/15.28  thf('59', plain,
% 15.10/15.28      (![X11 : $i, X12 : $i]:
% 15.10/15.28         (~ (r2_hidden @ 
% 15.10/15.28             (k4_tarski @ (sk_C @ X11 @ X12) @ (sk_E @ X11 @ X12)) @ X12)
% 15.10/15.28          | (r8_relat_2 @ X12 @ X11)
% 15.10/15.28          | ~ (v1_relat_1 @ X12))),
% 15.10/15.28      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.10/15.28  thf('60', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         (~ (l1_orders_2 @ X0)
% 15.10/15.28          | ~ (v4_orders_2 @ X0)
% 15.10/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.10/15.28          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.10/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.10/15.28      inference('sup-', [status(thm)], ['58', '59'])).
% 15.10/15.28  thf('61', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         (~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 15.10/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.10/15.28          | ~ (v4_orders_2 @ X0)
% 15.10/15.28          | ~ (l1_orders_2 @ X0))),
% 15.10/15.28      inference('simplify', [status(thm)], ['60'])).
% 15.10/15.28  thf('62', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         (~ (l1_orders_2 @ X0)
% 15.10/15.28          | ~ (l1_orders_2 @ X0)
% 15.10/15.28          | ~ (v4_orders_2 @ X0)
% 15.10/15.28          | (r8_relat_2 @ (u1_orders_2 @ X0) @ X1))),
% 15.10/15.28      inference('sup-', [status(thm)], ['20', '61'])).
% 15.10/15.28  thf('63', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         ((r8_relat_2 @ (u1_orders_2 @ X0) @ X1)
% 15.10/15.28          | ~ (v4_orders_2 @ X0)
% 15.10/15.28          | ~ (l1_orders_2 @ X0))),
% 15.10/15.28      inference('simplify', [status(thm)], ['62'])).
% 15.10/15.28  thf('64', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('65', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('66', plain,
% 15.10/15.28      (![X18 : $i, X19 : $i, X20 : $i]:
% 15.10/15.28         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 15.10/15.28          | ~ (r1_orders_2 @ X19 @ X18 @ X20)
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ X18 @ X20) @ (u1_orders_2 @ X19))
% 15.10/15.28          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 15.10/15.28          | ~ (l1_orders_2 @ X19))),
% 15.10/15.28      inference('cnf', [status(esa)], [d9_orders_2])).
% 15.10/15.28  thf('67', plain,
% 15.10/15.28      (![X0 : $i]:
% 15.10/15.28         (~ (l1_orders_2 @ sk_A)
% 15.10/15.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 15.10/15.28          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 15.10/15.28      inference('sup-', [status(thm)], ['65', '66'])).
% 15.10/15.28  thf('68', plain, ((l1_orders_2 @ sk_A)),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('69', plain,
% 15.10/15.28      (![X0 : $i]:
% 15.10/15.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 15.10/15.28          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 15.10/15.28      inference('demod', [status(thm)], ['67', '68'])).
% 15.10/15.28  thf('70', plain,
% 15.10/15.28      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1)
% 15.10/15.28        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['64', '69'])).
% 15.10/15.28  thf('71', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1)),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('72', plain,
% 15.10/15.28      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 15.10/15.28      inference('demod', [status(thm)], ['70', '71'])).
% 15.10/15.28  thf('73', plain,
% 15.10/15.28      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['18', '19'])).
% 15.10/15.28  thf('74', plain,
% 15.10/15.28      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 15.10/15.28      inference('demod', [status(thm)], ['7', '8'])).
% 15.10/15.28  thf('75', plain,
% 15.10/15.28      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 15.10/15.28         (~ (r8_relat_2 @ X12 @ X13)
% 15.10/15.28          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X12)
% 15.10/15.28          | ~ (r2_hidden @ X15 @ X13)
% 15.10/15.28          | ~ (r2_hidden @ X14 @ X13)
% 15.10/15.28          | ~ (r2_hidden @ X16 @ X13)
% 15.10/15.28          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X12)
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ X12)
% 15.10/15.28          | ~ (v1_relat_1 @ X12))),
% 15.10/15.28      inference('cnf', [status(esa)], [d8_relat_2])).
% 15.10/15.28  thf('76', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 15.10/15.28          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 15.10/15.28          | ~ (r2_hidden @ X0 @ X1)
% 15.10/15.28          | ~ (r2_hidden @ sk_B @ X1)
% 15.10/15.28          | ~ (r2_hidden @ sk_C_1 @ X1)
% 15.10/15.28          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X1))),
% 15.10/15.28      inference('sup-', [status(thm)], ['74', '75'])).
% 15.10/15.28  thf('77', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         (~ (l1_orders_2 @ sk_A)
% 15.10/15.28          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_C_1 @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_B @ X0)
% 15.10/15.28          | ~ (r2_hidden @ X1 @ X0)
% 15.10/15.28          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X1) @ (u1_orders_2 @ sk_A))
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ sk_B @ X1) @ (u1_orders_2 @ sk_A)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['73', '76'])).
% 15.10/15.28  thf('78', plain, ((l1_orders_2 @ sk_A)),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('79', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         (~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_C_1 @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_B @ X0)
% 15.10/15.28          | ~ (r2_hidden @ X1 @ X0)
% 15.10/15.28          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X1) @ (u1_orders_2 @ sk_A))
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ sk_B @ X1) @ (u1_orders_2 @ sk_A)))),
% 15.10/15.28      inference('demod', [status(thm)], ['77', '78'])).
% 15.10/15.28  thf('80', plain,
% 15.10/15.28      (![X0 : $i]:
% 15.10/15.28         ((r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 15.10/15.28          | ~ (r2_hidden @ sk_D_1 @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_B @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_C_1 @ X0)
% 15.10/15.28          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 15.10/15.28      inference('sup-', [status(thm)], ['72', '79'])).
% 15.10/15.28  thf('81', plain,
% 15.10/15.28      (![X0 : $i]:
% 15.10/15.28         (~ (l1_orders_2 @ sk_A)
% 15.10/15.28          | ~ (v4_orders_2 @ sk_A)
% 15.10/15.28          | ~ (r2_hidden @ sk_C_1 @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_B @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_D_1 @ X0)
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['63', '80'])).
% 15.10/15.28  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('84', plain,
% 15.10/15.28      (![X0 : $i]:
% 15.10/15.28         (~ (r2_hidden @ sk_C_1 @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_B @ X0)
% 15.10/15.28          | ~ (r2_hidden @ sk_D_1 @ X0)
% 15.10/15.28          | (r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 15.10/15.28      inference('demod', [status(thm)], ['81', '82', '83'])).
% 15.10/15.28  thf('85', plain,
% 15.10/15.28      (((r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 15.10/15.28        | ~ (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 15.10/15.28        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['17', '84'])).
% 15.10/15.28  thf('86', plain,
% 15.10/15.28      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 15.10/15.28      inference('demod', [status(thm)], ['70', '71'])).
% 15.10/15.28  thf('87', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i]:
% 15.10/15.28         (~ (l1_orders_2 @ X0)
% 15.10/15.28          | (r2_hidden @ X1 @ 
% 15.10/15.28             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 15.10/15.28          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['10', '11'])).
% 15.10/15.28  thf('88', plain,
% 15.10/15.28      (((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ 
% 15.10/15.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 15.10/15.28        | ~ (l1_orders_2 @ sk_A))),
% 15.10/15.28      inference('sup-', [status(thm)], ['86', '87'])).
% 15.10/15.28  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('90', plain,
% 15.10/15.28      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ 
% 15.10/15.28        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 15.10/15.28      inference('demod', [status(thm)], ['88', '89'])).
% 15.10/15.28  thf('91', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.10/15.28         ((r2_hidden @ X2 @ X3)
% 15.10/15.28          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.10/15.28      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.10/15.28  thf('92', plain, ((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 15.10/15.28      inference('sup-', [status(thm)], ['90', '91'])).
% 15.10/15.28  thf('93', plain,
% 15.10/15.28      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 15.10/15.28        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 15.10/15.28      inference('demod', [status(thm)], ['13', '14'])).
% 15.10/15.28  thf('94', plain,
% 15.10/15.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.10/15.28         ((r2_hidden @ X0 @ X1)
% 15.10/15.28          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 15.10/15.28      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 15.10/15.28  thf('95', plain, ((r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))),
% 15.10/15.28      inference('sup-', [status(thm)], ['93', '94'])).
% 15.10/15.28  thf('96', plain,
% 15.10/15.28      ((r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 15.10/15.28      inference('demod', [status(thm)], ['85', '92', '95'])).
% 15.10/15.28  thf('97', plain,
% 15.10/15.28      (![X18 : $i, X19 : $i, X20 : $i]:
% 15.10/15.28         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 15.10/15.28          | ~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ (u1_orders_2 @ X19))
% 15.10/15.28          | (r1_orders_2 @ X19 @ X18 @ X20)
% 15.10/15.28          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 15.10/15.28          | ~ (l1_orders_2 @ X19))),
% 15.10/15.28      inference('cnf', [status(esa)], [d9_orders_2])).
% 15.10/15.28  thf('98', plain,
% 15.10/15.28      ((~ (l1_orders_2 @ sk_A)
% 15.10/15.28        | ~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 15.10/15.28        | (r1_orders_2 @ sk_A @ sk_B @ sk_D_1)
% 15.10/15.28        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 15.10/15.28      inference('sup-', [status(thm)], ['96', '97'])).
% 15.10/15.28  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('100', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 15.10/15.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.28  thf('102', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_D_1)),
% 15.10/15.28      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 15.10/15.28  thf('103', plain, ($false), inference('demod', [status(thm)], ['0', '102'])).
% 15.10/15.28  
% 15.10/15.28  % SZS output end Refutation
% 15.10/15.28  
% 15.10/15.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
