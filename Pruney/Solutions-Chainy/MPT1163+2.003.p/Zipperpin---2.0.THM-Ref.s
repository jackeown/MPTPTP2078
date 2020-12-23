%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n0isowz8WF

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:04 EST 2020

% Result     : Theorem 3.26s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 613 expanded)
%              Number of leaves         :   23 ( 188 expanded)
%              Depth                    :   30
%              Number of atoms          : 1774 (13627 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t65_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r1_tarski @ C @ D )
                   => ( r1_tarski @ ( k3_orders_2 @ A @ C @ B ) @ ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( r1_tarski @ C @ D )
                     => ( r1_tarski @ ( k3_orders_2 @ A @ C @ B ) @ ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_orders_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X10 @ X9 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X10 @ X9 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_orders_2 @ X13 @ X12 @ X15 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ( r2_hidden @ X12 @ ( k3_orders_2 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('42',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k3_orders_2 @ X13 @ X14 @ X15 ) )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['57','73'])).

thf('75',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('83',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_C ),
    inference(simplify,[status(thm)],['83'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('85',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['52','88'])).

thf('90',plain,(
    r1_tarski @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_D_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('101',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_D_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ sk_D_1 ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['47','106'])).

thf('108',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k3_orders_2 @ X13 @ X14 @ X15 ) )
      | ( r2_orders_2 @ X13 @ X12 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','116'])).

thf('118',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','107','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('127',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('131',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['0','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n0isowz8WF
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:00:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 3.26/3.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.26/3.51  % Solved by: fo/fo7.sh
% 3.26/3.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.26/3.51  % done 2032 iterations in 3.048s
% 3.26/3.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.26/3.51  % SZS output start Refutation
% 3.26/3.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.26/3.51  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 3.26/3.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 3.26/3.51  thf(sk_C_type, type, sk_C: $i).
% 3.26/3.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.26/3.51  thf(sk_B_type, type, sk_B: $i).
% 3.26/3.51  thf(sk_A_type, type, sk_A: $i).
% 3.26/3.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 3.26/3.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 3.26/3.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.26/3.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.26/3.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 3.26/3.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.26/3.51  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 3.26/3.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 3.26/3.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.26/3.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.26/3.51  thf(t65_orders_2, conjecture,
% 3.26/3.51    (![A:$i]:
% 3.26/3.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.26/3.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.26/3.51       ( ![B:$i]:
% 3.26/3.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.26/3.51           ( ![C:$i]:
% 3.26/3.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.26/3.51               ( ![D:$i]:
% 3.26/3.51                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.26/3.51                   ( ( r1_tarski @ C @ D ) =>
% 3.26/3.51                     ( r1_tarski @
% 3.26/3.51                       ( k3_orders_2 @ A @ C @ B ) @ 
% 3.26/3.51                       ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 3.26/3.51  thf(zf_stmt_0, negated_conjecture,
% 3.26/3.51    (~( ![A:$i]:
% 3.26/3.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.26/3.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.26/3.51          ( ![B:$i]:
% 3.26/3.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.26/3.51              ( ![C:$i]:
% 3.26/3.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.26/3.51                  ( ![D:$i]:
% 3.26/3.51                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.26/3.51                      ( ( r1_tarski @ C @ D ) =>
% 3.26/3.51                        ( r1_tarski @
% 3.26/3.51                          ( k3_orders_2 @ A @ C @ B ) @ 
% 3.26/3.51                          ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 3.26/3.51    inference('cnf.neg', [status(esa)], [t65_orders_2])).
% 3.26/3.51  thf('0', plain,
% 3.26/3.51      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('2', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf(dt_k3_orders_2, axiom,
% 3.26/3.51    (![A:$i,B:$i,C:$i]:
% 3.26/3.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.26/3.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 3.26/3.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 3.26/3.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 3.26/3.51       ( m1_subset_1 @
% 3.26/3.51         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.26/3.51  thf('3', plain,
% 3.26/3.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 3.26/3.51          | ~ (l1_orders_2 @ X10)
% 3.26/3.51          | ~ (v5_orders_2 @ X10)
% 3.26/3.51          | ~ (v4_orders_2 @ X10)
% 3.26/3.51          | ~ (v3_orders_2 @ X10)
% 3.26/3.51          | (v2_struct_0 @ X10)
% 3.26/3.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 3.26/3.51          | (m1_subset_1 @ (k3_orders_2 @ X10 @ X9 @ X11) @ 
% 3.26/3.51             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 3.26/3.51      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 3.26/3.51  thf('4', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ X0) @ 
% 3.26/3.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (v2_struct_0 @ sk_A)
% 3.26/3.51          | ~ (v3_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v4_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v5_orders_2 @ sk_A)
% 3.26/3.51          | ~ (l1_orders_2 @ sk_A))),
% 3.26/3.51      inference('sup-', [status(thm)], ['2', '3'])).
% 3.26/3.51  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('6', plain, ((v4_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('9', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ X0) @ 
% 3.26/3.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (v2_struct_0 @ sk_A))),
% 3.26/3.51      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 3.26/3.51  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('11', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ X0) @ 
% 3.26/3.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.26/3.51      inference('clc', [status(thm)], ['9', '10'])).
% 3.26/3.51  thf('12', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['1', '11'])).
% 3.26/3.51  thf('13', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('14', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('15', plain,
% 3.26/3.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 3.26/3.51          | ~ (l1_orders_2 @ X10)
% 3.26/3.51          | ~ (v5_orders_2 @ X10)
% 3.26/3.51          | ~ (v4_orders_2 @ X10)
% 3.26/3.51          | ~ (v3_orders_2 @ X10)
% 3.26/3.51          | (v2_struct_0 @ X10)
% 3.26/3.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 3.26/3.51          | (m1_subset_1 @ (k3_orders_2 @ X10 @ X9 @ X11) @ 
% 3.26/3.51             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 3.26/3.51      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 3.26/3.51  thf('16', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 3.26/3.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (v2_struct_0 @ sk_A)
% 3.26/3.51          | ~ (v3_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v4_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v5_orders_2 @ sk_A)
% 3.26/3.51          | ~ (l1_orders_2 @ sk_A))),
% 3.26/3.51      inference('sup-', [status(thm)], ['14', '15'])).
% 3.26/3.51  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('18', plain, ((v4_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('21', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 3.26/3.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (v2_struct_0 @ sk_A))),
% 3.26/3.51      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 3.26/3.51  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('23', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 3.26/3.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.26/3.51      inference('clc', [status(thm)], ['21', '22'])).
% 3.26/3.51  thf('24', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['13', '23'])).
% 3.26/3.51  thf(t7_subset_1, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.26/3.51       ( ![C:$i]:
% 3.26/3.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.26/3.51           ( ( ![D:$i]:
% 3.26/3.51               ( ( m1_subset_1 @ D @ A ) =>
% 3.26/3.51                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 3.26/3.51             ( r1_tarski @ B @ C ) ) ) ) ))).
% 3.26/3.51  thf('25', plain,
% 3.26/3.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.26/3.51          | (r1_tarski @ X5 @ X3)
% 3.26/3.51          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 3.26/3.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.26/3.51  thf('26', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | (m1_subset_1 @ 
% 3.26/3.51             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 3.26/3.51              (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51             (u1_struct_0 @ sk_A))
% 3.26/3.51          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['24', '25'])).
% 3.26/3.51  thf('27', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.26/3.51        | (m1_subset_1 @ 
% 3.26/3.51           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51            (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['12', '26'])).
% 3.26/3.51  thf('28', plain,
% 3.26/3.51      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('29', plain,
% 3.26/3.51      ((m1_subset_1 @ 
% 3.26/3.51        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51        (u1_struct_0 @ sk_A))),
% 3.26/3.51      inference('clc', [status(thm)], ['27', '28'])).
% 3.26/3.51  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('31', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf(t57_orders_2, axiom,
% 3.26/3.51    (![A:$i]:
% 3.26/3.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.26/3.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.26/3.51       ( ![B:$i]:
% 3.26/3.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.26/3.51           ( ![C:$i]:
% 3.26/3.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.26/3.51               ( ![D:$i]:
% 3.26/3.51                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.26/3.51                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 3.26/3.51                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 3.26/3.51  thf('32', plain,
% 3.26/3.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 3.26/3.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 3.26/3.51          | ~ (r2_orders_2 @ X13 @ X12 @ X15)
% 3.26/3.51          | ~ (r2_hidden @ X12 @ X14)
% 3.26/3.51          | (r2_hidden @ X12 @ (k3_orders_2 @ X13 @ X14 @ X15))
% 3.26/3.51          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 3.26/3.51          | ~ (l1_orders_2 @ X13)
% 3.26/3.51          | ~ (v5_orders_2 @ X13)
% 3.26/3.51          | ~ (v4_orders_2 @ X13)
% 3.26/3.51          | ~ (v3_orders_2 @ X13)
% 3.26/3.51          | (v2_struct_0 @ X13))),
% 3.26/3.51      inference('cnf', [status(esa)], [t57_orders_2])).
% 3.26/3.51  thf('33', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((v2_struct_0 @ sk_A)
% 3.26/3.51          | ~ (v3_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v4_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v5_orders_2 @ sk_A)
% 3.26/3.51          | ~ (l1_orders_2 @ sk_A)
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 3.26/3.51          | ~ (r2_hidden @ X1 @ sk_D_1)
% 3.26/3.51          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['31', '32'])).
% 3.26/3.51  thf('34', plain, ((v3_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('35', plain, ((v4_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('36', plain, ((v5_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('38', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((v2_struct_0 @ sk_A)
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 3.26/3.51          | ~ (r2_hidden @ X1 @ sk_D_1)
% 3.26/3.51          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 3.26/3.51  thf('39', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 3.26/3.51          | ~ (r2_hidden @ X0 @ sk_D_1)
% 3.26/3.51          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.26/3.51          | (v2_struct_0 @ sk_A))),
% 3.26/3.51      inference('sup-', [status(thm)], ['30', '38'])).
% 3.26/3.51  thf('40', plain,
% 3.26/3.51      (((v2_struct_0 @ sk_A)
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51            (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.26/3.51        | ~ (r2_hidden @ 
% 3.26/3.51             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51              (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51             sk_D_1)
% 3.26/3.51        | ~ (r2_orders_2 @ sk_A @ 
% 3.26/3.51             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51              (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51             sk_B))),
% 3.26/3.51      inference('sup-', [status(thm)], ['29', '39'])).
% 3.26/3.51  thf('41', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['1', '11'])).
% 3.26/3.51  thf('42', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['13', '23'])).
% 3.26/3.51  thf('43', plain,
% 3.26/3.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.26/3.51          | (r1_tarski @ X5 @ X3)
% 3.26/3.51          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 3.26/3.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.26/3.51  thf('44', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | (r2_hidden @ 
% 3.26/3.51             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 3.26/3.51              (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51             X0)
% 3.26/3.51          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['42', '43'])).
% 3.26/3.51  thf('45', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51            (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           (k3_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['41', '44'])).
% 3.26/3.51  thf('46', plain,
% 3.26/3.51      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('47', plain,
% 3.26/3.51      ((r2_hidden @ 
% 3.26/3.51        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51        (k3_orders_2 @ sk_A @ sk_C @ sk_B))),
% 3.26/3.51      inference('clc', [status(thm)], ['45', '46'])).
% 3.26/3.51  thf('48', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['1', '11'])).
% 3.26/3.51  thf('49', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('50', plain,
% 3.26/3.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.26/3.51          | (r1_tarski @ X5 @ X3)
% 3.26/3.51          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 3.26/3.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.26/3.51  thf('51', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | (r2_hidden @ (sk_D @ sk_D_1 @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.26/3.51          | (r1_tarski @ X0 @ sk_D_1))),
% 3.26/3.51      inference('sup-', [status(thm)], ['49', '50'])).
% 3.26/3.51  thf('52', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_D_1)
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ sk_D_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           (k3_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['48', '51'])).
% 3.26/3.51  thf('53', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['1', '11'])).
% 3.26/3.51  thf('54', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('55', plain,
% 3.26/3.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.26/3.51          | (r1_tarski @ X5 @ X3)
% 3.26/3.51          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 3.26/3.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.26/3.51  thf('56', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | (m1_subset_1 @ (sk_D @ sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51             (u1_struct_0 @ sk_A))
% 3.26/3.51          | (r1_tarski @ X0 @ sk_C))),
% 3.26/3.51      inference('sup-', [status(thm)], ['54', '55'])).
% 3.26/3.51  thf('57', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | (m1_subset_1 @ 
% 3.26/3.51           (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['53', '56'])).
% 3.26/3.51  thf('58', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['1', '11'])).
% 3.26/3.51  thf('59', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('60', plain,
% 3.26/3.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.26/3.51          | (r1_tarski @ X5 @ X3)
% 3.26/3.51          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 3.26/3.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.26/3.51  thf('61', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | (r2_hidden @ (sk_D @ sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.26/3.51          | (r1_tarski @ X0 @ sk_C))),
% 3.26/3.51      inference('sup-', [status(thm)], ['59', '60'])).
% 3.26/3.51  thf('62', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           (k3_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['58', '61'])).
% 3.26/3.51  thf('63', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('64', plain,
% 3.26/3.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 3.26/3.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 3.26/3.51          | ~ (r2_hidden @ X12 @ (k3_orders_2 @ X13 @ X14 @ X15))
% 3.26/3.51          | (r2_hidden @ X12 @ X14)
% 3.26/3.51          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 3.26/3.51          | ~ (l1_orders_2 @ X13)
% 3.26/3.51          | ~ (v5_orders_2 @ X13)
% 3.26/3.51          | ~ (v4_orders_2 @ X13)
% 3.26/3.51          | ~ (v3_orders_2 @ X13)
% 3.26/3.51          | (v2_struct_0 @ X13))),
% 3.26/3.51      inference('cnf', [status(esa)], [t57_orders_2])).
% 3.26/3.51  thf('65', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((v2_struct_0 @ sk_A)
% 3.26/3.51          | ~ (v3_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v4_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v5_orders_2 @ sk_A)
% 3.26/3.51          | ~ (l1_orders_2 @ sk_A)
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (r2_hidden @ X1 @ sk_C)
% 3.26/3.51          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C @ X0))
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['63', '64'])).
% 3.26/3.51  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('67', plain, ((v4_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('70', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((v2_struct_0 @ sk_A)
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (r2_hidden @ X1 @ sk_C)
% 3.26/3.51          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C @ X0))
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 3.26/3.51  thf('71', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | ~ (m1_subset_1 @ 
% 3.26/3.51             (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51              (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51             (u1_struct_0 @ sk_A))
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           sk_C)
% 3.26/3.51        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.26/3.51        | (v2_struct_0 @ sk_A))),
% 3.26/3.51      inference('sup-', [status(thm)], ['62', '70'])).
% 3.26/3.51  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('73', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | ~ (m1_subset_1 @ 
% 3.26/3.51             (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51              (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51             (u1_struct_0 @ sk_A))
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           sk_C)
% 3.26/3.51        | (v2_struct_0 @ sk_A))),
% 3.26/3.51      inference('demod', [status(thm)], ['71', '72'])).
% 3.26/3.51  thf('74', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | (v2_struct_0 @ sk_A)
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           sk_C)
% 3.26/3.51        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C))),
% 3.26/3.51      inference('sup-', [status(thm)], ['57', '73'])).
% 3.26/3.51  thf('75', plain,
% 3.26/3.51      (((r2_hidden @ 
% 3.26/3.51         (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51          (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51         sk_C)
% 3.26/3.51        | (v2_struct_0 @ sk_A)
% 3.26/3.51        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C))),
% 3.26/3.51      inference('simplify', [status(thm)], ['74'])).
% 3.26/3.51  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('77', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ sk_C @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           sk_C))),
% 3.26/3.51      inference('clc', [status(thm)], ['75', '76'])).
% 3.26/3.51  thf('78', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('79', plain,
% 3.26/3.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.26/3.51          | (r1_tarski @ X5 @ X3)
% 3.26/3.51          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 3.26/3.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.26/3.51  thf('80', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | ~ (r2_hidden @ (sk_D @ sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ sk_C)
% 3.26/3.51          | (r1_tarski @ X0 @ sk_C))),
% 3.26/3.51      inference('sup-', [status(thm)], ['78', '79'])).
% 3.26/3.51  thf('81', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.26/3.51      inference('sup-', [status(thm)], ['77', '80'])).
% 3.26/3.51  thf('82', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['1', '11'])).
% 3.26/3.51  thf('83', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)
% 3.26/3.51        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C))),
% 3.26/3.51      inference('demod', [status(thm)], ['81', '82'])).
% 3.26/3.51  thf('84', plain, ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_C)),
% 3.26/3.51      inference('simplify', [status(thm)], ['83'])).
% 3.26/3.51  thf(t3_subset, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.26/3.51  thf('85', plain,
% 3.26/3.51      (![X6 : $i, X8 : $i]:
% 3.26/3.51         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 3.26/3.51      inference('cnf', [status(esa)], [t3_subset])).
% 3.26/3.51  thf('86', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (k1_zfmisc_1 @ sk_C))),
% 3.26/3.51      inference('sup-', [status(thm)], ['84', '85'])).
% 3.26/3.51  thf(l3_subset_1, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.26/3.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 3.26/3.51  thf('87', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X0 @ X1)
% 3.26/3.51          | (r2_hidden @ X0 @ X2)
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 3.26/3.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 3.26/3.51  thf('88', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         ((r2_hidden @ X0 @ sk_C)
% 3.26/3.51          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['86', '87'])).
% 3.26/3.51  thf('89', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_D_1)
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ sk_D_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           sk_C))),
% 3.26/3.51      inference('sup-', [status(thm)], ['52', '88'])).
% 3.26/3.51  thf('90', plain, ((r1_tarski @ sk_C @ sk_D_1)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('91', plain,
% 3.26/3.51      (![X6 : $i, X8 : $i]:
% 3.26/3.51         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 3.26/3.51      inference('cnf', [status(esa)], [t3_subset])).
% 3.26/3.51  thf('92', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_D_1))),
% 3.26/3.51      inference('sup-', [status(thm)], ['90', '91'])).
% 3.26/3.51  thf('93', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X0 @ X1)
% 3.26/3.51          | (r2_hidden @ X0 @ X2)
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 3.26/3.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 3.26/3.51  thf('94', plain,
% 3.26/3.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_C))),
% 3.26/3.51      inference('sup-', [status(thm)], ['92', '93'])).
% 3.26/3.51  thf('95', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_D_1)
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ sk_D_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51            (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           sk_D_1))),
% 3.26/3.51      inference('sup-', [status(thm)], ['89', '94'])).
% 3.26/3.51  thf('96', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('97', plain,
% 3.26/3.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.26/3.51          | (r1_tarski @ X5 @ X3)
% 3.26/3.51          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 3.26/3.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.26/3.51  thf('98', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_D_1)
% 3.26/3.51          | (r1_tarski @ X0 @ sk_D_1))),
% 3.26/3.51      inference('sup-', [status(thm)], ['96', '97'])).
% 3.26/3.51  thf('99', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_D_1)
% 3.26/3.51        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_D_1)
% 3.26/3.51        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.26/3.51      inference('sup-', [status(thm)], ['95', '98'])).
% 3.26/3.51  thf('100', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['1', '11'])).
% 3.26/3.51  thf('101', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_D_1)
% 3.26/3.51        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_D_1))),
% 3.26/3.51      inference('demod', [status(thm)], ['99', '100'])).
% 3.26/3.51  thf('102', plain,
% 3.26/3.51      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ sk_D_1)),
% 3.26/3.51      inference('simplify', [status(thm)], ['101'])).
% 3.26/3.51  thf('103', plain,
% 3.26/3.51      (![X6 : $i, X8 : $i]:
% 3.26/3.51         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 3.26/3.51      inference('cnf', [status(esa)], [t3_subset])).
% 3.26/3.51  thf('104', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ sk_D_1))),
% 3.26/3.51      inference('sup-', [status(thm)], ['102', '103'])).
% 3.26/3.51  thf('105', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X0 @ X1)
% 3.26/3.51          | (r2_hidden @ X0 @ X2)
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 3.26/3.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 3.26/3.51  thf('106', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         ((r2_hidden @ X0 @ sk_D_1)
% 3.26/3.51          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['104', '105'])).
% 3.26/3.51  thf('107', plain,
% 3.26/3.51      ((r2_hidden @ 
% 3.26/3.51        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51        sk_D_1)),
% 3.26/3.51      inference('sup-', [status(thm)], ['47', '106'])).
% 3.26/3.51  thf('108', plain,
% 3.26/3.51      ((r2_hidden @ 
% 3.26/3.51        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51        (k3_orders_2 @ sk_A @ sk_C @ sk_B))),
% 3.26/3.51      inference('clc', [status(thm)], ['45', '46'])).
% 3.26/3.51  thf('109', plain,
% 3.26/3.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('110', plain,
% 3.26/3.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 3.26/3.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 3.26/3.51          | ~ (r2_hidden @ X12 @ (k3_orders_2 @ X13 @ X14 @ X15))
% 3.26/3.51          | (r2_orders_2 @ X13 @ X12 @ X15)
% 3.26/3.51          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 3.26/3.51          | ~ (l1_orders_2 @ X13)
% 3.26/3.51          | ~ (v5_orders_2 @ X13)
% 3.26/3.51          | ~ (v4_orders_2 @ X13)
% 3.26/3.51          | ~ (v3_orders_2 @ X13)
% 3.26/3.51          | (v2_struct_0 @ X13))),
% 3.26/3.51      inference('cnf', [status(esa)], [t57_orders_2])).
% 3.26/3.51  thf('111', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((v2_struct_0 @ sk_A)
% 3.26/3.51          | ~ (v3_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v4_orders_2 @ sk_A)
% 3.26/3.51          | ~ (v5_orders_2 @ sk_A)
% 3.26/3.51          | ~ (l1_orders_2 @ sk_A)
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 3.26/3.51          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C @ X0))
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['109', '110'])).
% 3.26/3.51  thf('112', plain, ((v3_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('113', plain, ((v4_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('114', plain, ((v5_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('115', plain, ((l1_orders_2 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('116', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((v2_struct_0 @ sk_A)
% 3.26/3.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.26/3.51          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 3.26/3.51          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C @ X0))
% 3.26/3.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 3.26/3.51  thf('117', plain,
% 3.26/3.51      ((~ (m1_subset_1 @ 
% 3.26/3.51           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51            (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           (u1_struct_0 @ sk_A))
% 3.26/3.51        | (r2_orders_2 @ sk_A @ 
% 3.26/3.51           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51            (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           sk_B)
% 3.26/3.51        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.26/3.51        | (v2_struct_0 @ sk_A))),
% 3.26/3.51      inference('sup-', [status(thm)], ['108', '116'])).
% 3.26/3.51  thf('118', plain,
% 3.26/3.51      ((m1_subset_1 @ 
% 3.26/3.51        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51        (u1_struct_0 @ sk_A))),
% 3.26/3.51      inference('clc', [status(thm)], ['27', '28'])).
% 3.26/3.51  thf('119', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('120', plain,
% 3.26/3.51      (((r2_orders_2 @ sk_A @ 
% 3.26/3.51         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51          (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51         sk_B)
% 3.26/3.51        | (v2_struct_0 @ sk_A))),
% 3.26/3.51      inference('demod', [status(thm)], ['117', '118', '119'])).
% 3.26/3.51  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('122', plain,
% 3.26/3.51      ((r2_orders_2 @ sk_A @ 
% 3.26/3.51        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51        sk_B)),
% 3.26/3.51      inference('clc', [status(thm)], ['120', '121'])).
% 3.26/3.51  thf('123', plain,
% 3.26/3.51      (((v2_struct_0 @ sk_A)
% 3.26/3.51        | (r2_hidden @ 
% 3.26/3.51           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51            (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 3.26/3.51      inference('demod', [status(thm)], ['40', '107', '122'])).
% 3.26/3.51  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('125', plain,
% 3.26/3.51      ((r2_hidden @ 
% 3.26/3.51        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.26/3.51      inference('clc', [status(thm)], ['123', '124'])).
% 3.26/3.51  thf('126', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['13', '23'])).
% 3.26/3.51  thf('127', plain,
% 3.26/3.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.26/3.51          | (r1_tarski @ X5 @ X3)
% 3.26/3.51          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 3.26/3.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.26/3.51  thf('128', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.26/3.51          | ~ (r2_hidden @ 
% 3.26/3.51               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 3.26/3.51                (u1_struct_0 @ sk_A)) @ 
% 3.26/3.51               (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.26/3.51          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['126', '127'])).
% 3.26/3.51  thf('129', plain,
% 3.26/3.51      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.26/3.51        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.26/3.51      inference('sup-', [status(thm)], ['125', '128'])).
% 3.26/3.51  thf('130', plain,
% 3.26/3.51      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['1', '11'])).
% 3.26/3.51  thf('131', plain,
% 3.26/3.51      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C @ sk_B) @ 
% 3.26/3.51        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.26/3.51      inference('demod', [status(thm)], ['129', '130'])).
% 3.26/3.51  thf('132', plain, ($false), inference('demod', [status(thm)], ['0', '131'])).
% 3.35/3.51  
% 3.35/3.51  % SZS output end Refutation
% 3.35/3.51  
% 3.35/3.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
