%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BaJr4GULLO

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:04 EST 2020

% Result     : Theorem 6.90s
% Output     : Refutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 564 expanded)
%              Number of leaves         :   22 ( 174 expanded)
%              Depth                    :   20
%              Number of atoms          : 1438 (12968 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t64_orders_2,conjecture,(
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
                 => ( ( r2_orders_2 @ A @ B @ C )
                   => ( r1_tarski @ ( k3_orders_2 @ A @ D @ B ) @ ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) )).

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
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( r2_orders_2 @ A @ B @ C )
                     => ( r1_tarski @ ( k3_orders_2 @ A @ D @ B ) @ ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_orders_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X4 @ X3 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('15',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_orders_2 @ X11 @ X10 @ X13 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('33',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
    | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['31','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k3_orders_2 @ X11 @ X12 @ X13 ) )
      | ( r2_orders_2 @ X11 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t29_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_orders_2 @ A @ C @ D ) )
                   => ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf('73',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( r2_orders_2 @ X7 @ X6 @ X8 )
      | ~ ( r2_orders_2 @ X7 @ X9 @ X8 )
      | ~ ( r2_orders_2 @ X7 @ X6 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_orders_2])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['56','81'])).

thf('83',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('91',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BaJr4GULLO
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.90/7.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.90/7.11  % Solved by: fo/fo7.sh
% 6.90/7.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.90/7.11  % done 1801 iterations in 6.655s
% 6.90/7.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.90/7.11  % SZS output start Refutation
% 6.90/7.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.90/7.11  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 6.90/7.11  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 6.90/7.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.90/7.11  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 6.90/7.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.90/7.11  thf(sk_A_type, type, sk_A: $i).
% 6.90/7.11  thf(sk_C_type, type, sk_C: $i).
% 6.90/7.11  thf(sk_D_1_type, type, sk_D_1: $i).
% 6.90/7.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.90/7.11  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 6.90/7.11  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 6.90/7.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.90/7.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.90/7.11  thf(sk_B_type, type, sk_B: $i).
% 6.90/7.11  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.90/7.11  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 6.90/7.11  thf(t64_orders_2, conjecture,
% 6.90/7.11    (![A:$i]:
% 6.90/7.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.90/7.11         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 6.90/7.11       ( ![B:$i]:
% 6.90/7.11         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11           ( ![C:$i]:
% 6.90/7.11             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11               ( ![D:$i]:
% 6.90/7.11                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.90/7.11                   ( ( r2_orders_2 @ A @ B @ C ) =>
% 6.90/7.11                     ( r1_tarski @
% 6.90/7.11                       ( k3_orders_2 @ A @ D @ B ) @ 
% 6.90/7.11                       ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 6.90/7.11  thf(zf_stmt_0, negated_conjecture,
% 6.90/7.11    (~( ![A:$i]:
% 6.90/7.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.90/7.11            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 6.90/7.11          ( ![B:$i]:
% 6.90/7.11            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11              ( ![C:$i]:
% 6.90/7.11                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11                  ( ![D:$i]:
% 6.90/7.11                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.90/7.11                      ( ( r2_orders_2 @ A @ B @ C ) =>
% 6.90/7.11                        ( r1_tarski @
% 6.90/7.11                          ( k3_orders_2 @ A @ D @ B ) @ 
% 6.90/7.11                          ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 6.90/7.11    inference('cnf.neg', [status(esa)], [t64_orders_2])).
% 6.90/7.11  thf('0', plain,
% 6.90/7.11      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.11          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('2', plain,
% 6.90/7.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf(dt_k3_orders_2, axiom,
% 6.90/7.11    (![A:$i,B:$i,C:$i]:
% 6.90/7.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.90/7.11         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 6.90/7.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 6.90/7.11         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 6.90/7.11       ( m1_subset_1 @
% 6.90/7.11         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.90/7.11  thf('3', plain,
% 6.90/7.11      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 6.90/7.11          | ~ (l1_orders_2 @ X4)
% 6.90/7.11          | ~ (v5_orders_2 @ X4)
% 6.90/7.11          | ~ (v4_orders_2 @ X4)
% 6.90/7.11          | ~ (v3_orders_2 @ X4)
% 6.90/7.11          | (v2_struct_0 @ X4)
% 6.90/7.11          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 6.90/7.11          | (m1_subset_1 @ (k3_orders_2 @ X4 @ X3 @ X5) @ 
% 6.90/7.11             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 6.90/7.11      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 6.90/7.11  thf('4', plain,
% 6.90/7.11      (![X0 : $i]:
% 6.90/7.11         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 6.90/7.11           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.90/7.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (v2_struct_0 @ sk_A)
% 6.90/7.11          | ~ (v3_orders_2 @ sk_A)
% 6.90/7.11          | ~ (v4_orders_2 @ sk_A)
% 6.90/7.11          | ~ (v5_orders_2 @ sk_A)
% 6.90/7.11          | ~ (l1_orders_2 @ sk_A))),
% 6.90/7.11      inference('sup-', [status(thm)], ['2', '3'])).
% 6.90/7.11  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('6', plain, ((v4_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('9', plain,
% 6.90/7.11      (![X0 : $i]:
% 6.90/7.11         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 6.90/7.11           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.90/7.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (v2_struct_0 @ sk_A))),
% 6.90/7.11      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 6.90/7.11  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('11', plain,
% 6.90/7.11      (![X0 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 6.90/7.11             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.90/7.11      inference('clc', [status(thm)], ['9', '10'])).
% 6.90/7.11  thf('12', plain,
% 6.90/7.11      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['1', '11'])).
% 6.90/7.11  thf('13', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('14', plain,
% 6.90/7.11      (![X0 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 6.90/7.11             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.90/7.11      inference('clc', [status(thm)], ['9', '10'])).
% 6.90/7.11  thf('15', plain,
% 6.90/7.11      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['13', '14'])).
% 6.90/7.11  thf(t7_subset_1, axiom,
% 6.90/7.11    (![A:$i,B:$i]:
% 6.90/7.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.90/7.11       ( ![C:$i]:
% 6.90/7.11         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.90/7.11           ( ( ![D:$i]:
% 6.90/7.11               ( ( m1_subset_1 @ D @ A ) =>
% 6.90/7.11                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 6.90/7.11             ( r1_tarski @ B @ C ) ) ) ) ))).
% 6.90/7.11  thf('16', plain,
% 6.90/7.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 6.90/7.11          | (r1_tarski @ X2 @ X0)
% 6.90/7.11          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 6.90/7.11          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 6.90/7.11      inference('cnf', [status(esa)], [t7_subset_1])).
% 6.90/7.11  thf('17', plain,
% 6.90/7.11      (![X0 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.90/7.11          | (m1_subset_1 @ 
% 6.90/7.11             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ X0 @ 
% 6.90/7.11              (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11             (u1_struct_0 @ sk_A))
% 6.90/7.11          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['15', '16'])).
% 6.90/7.11  thf('18', plain,
% 6.90/7.11      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 6.90/7.11        | (m1_subset_1 @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['12', '17'])).
% 6.90/7.11  thf('19', plain,
% 6.90/7.11      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.11          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('20', plain,
% 6.90/7.11      ((m1_subset_1 @ 
% 6.90/7.11        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11        (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('clc', [status(thm)], ['18', '19'])).
% 6.90/7.11  thf('21', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('22', plain,
% 6.90/7.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf(t57_orders_2, axiom,
% 6.90/7.11    (![A:$i]:
% 6.90/7.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.90/7.11         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 6.90/7.11       ( ![B:$i]:
% 6.90/7.11         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11           ( ![C:$i]:
% 6.90/7.11             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11               ( ![D:$i]:
% 6.90/7.11                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.90/7.11                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 6.90/7.11                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 6.90/7.11  thf('23', plain,
% 6.90/7.11      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 6.90/7.11          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 6.90/7.11          | ~ (r2_orders_2 @ X11 @ X10 @ X13)
% 6.90/7.11          | ~ (r2_hidden @ X10 @ X12)
% 6.90/7.11          | (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 6.90/7.11          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 6.90/7.11          | ~ (l1_orders_2 @ X11)
% 6.90/7.11          | ~ (v5_orders_2 @ X11)
% 6.90/7.11          | ~ (v4_orders_2 @ X11)
% 6.90/7.11          | ~ (v3_orders_2 @ X11)
% 6.90/7.11          | (v2_struct_0 @ X11))),
% 6.90/7.11      inference('cnf', [status(esa)], [t57_orders_2])).
% 6.90/7.11  thf('24', plain,
% 6.90/7.11      (![X0 : $i, X1 : $i]:
% 6.90/7.11         ((v2_struct_0 @ sk_A)
% 6.90/7.11          | ~ (v3_orders_2 @ sk_A)
% 6.90/7.11          | ~ (v4_orders_2 @ sk_A)
% 6.90/7.11          | ~ (v5_orders_2 @ sk_A)
% 6.90/7.11          | ~ (l1_orders_2 @ sk_A)
% 6.90/7.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 6.90/7.11          | ~ (r2_hidden @ X1 @ sk_D_1)
% 6.90/7.11          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 6.90/7.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['22', '23'])).
% 6.90/7.11  thf('25', plain, ((v3_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('27', plain, ((v5_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('29', plain,
% 6.90/7.11      (![X0 : $i, X1 : $i]:
% 6.90/7.11         ((v2_struct_0 @ sk_A)
% 6.90/7.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 6.90/7.11          | ~ (r2_hidden @ X1 @ sk_D_1)
% 6.90/7.11          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 6.90/7.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 6.90/7.11  thf('30', plain,
% 6.90/7.11      (![X0 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C)
% 6.90/7.11          | ~ (r2_hidden @ X0 @ sk_D_1)
% 6.90/7.11          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 6.90/7.11          | (v2_struct_0 @ sk_A))),
% 6.90/7.11      inference('sup-', [status(thm)], ['21', '29'])).
% 6.90/7.11  thf('31', plain,
% 6.90/7.11      (((v2_struct_0 @ sk_A)
% 6.90/7.11        | (r2_hidden @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 6.90/7.11        | ~ (r2_hidden @ 
% 6.90/7.11             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11             sk_D_1)
% 6.90/7.11        | ~ (r2_orders_2 @ sk_A @ 
% 6.90/7.11             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11             sk_C))),
% 6.90/7.11      inference('sup-', [status(thm)], ['20', '30'])).
% 6.90/7.11  thf('32', plain,
% 6.90/7.11      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['1', '11'])).
% 6.90/7.11  thf('33', plain,
% 6.90/7.11      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['13', '14'])).
% 6.90/7.11  thf('34', plain,
% 6.90/7.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 6.90/7.11          | (r1_tarski @ X2 @ X0)
% 6.90/7.11          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 6.90/7.11          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 6.90/7.11      inference('cnf', [status(esa)], [t7_subset_1])).
% 6.90/7.11  thf('35', plain,
% 6.90/7.11      (![X0 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.90/7.11          | (r2_hidden @ 
% 6.90/7.11             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ X0 @ 
% 6.90/7.11              (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11             X0)
% 6.90/7.11          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['33', '34'])).
% 6.90/7.11  thf('36', plain,
% 6.90/7.11      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 6.90/7.11        | (r2_hidden @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['32', '35'])).
% 6.90/7.11  thf('37', plain,
% 6.90/7.11      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.11          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('38', plain,
% 6.90/7.11      ((r2_hidden @ 
% 6.90/7.11        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 6.90/7.11      inference('clc', [status(thm)], ['36', '37'])).
% 6.90/7.11  thf('39', plain,
% 6.90/7.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('40', plain,
% 6.90/7.11      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 6.90/7.11          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 6.90/7.11          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 6.90/7.11          | (r2_hidden @ X10 @ X12)
% 6.90/7.11          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 6.90/7.11          | ~ (l1_orders_2 @ X11)
% 6.90/7.11          | ~ (v5_orders_2 @ X11)
% 6.90/7.11          | ~ (v4_orders_2 @ X11)
% 6.90/7.11          | ~ (v3_orders_2 @ X11)
% 6.90/7.11          | (v2_struct_0 @ X11))),
% 6.90/7.11      inference('cnf', [status(esa)], [t57_orders_2])).
% 6.90/7.11  thf('41', plain,
% 6.90/7.11      (![X0 : $i, X1 : $i]:
% 6.90/7.11         ((v2_struct_0 @ sk_A)
% 6.90/7.11          | ~ (v3_orders_2 @ sk_A)
% 6.90/7.11          | ~ (v4_orders_2 @ sk_A)
% 6.90/7.11          | ~ (v5_orders_2 @ sk_A)
% 6.90/7.11          | ~ (l1_orders_2 @ sk_A)
% 6.90/7.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (r2_hidden @ X1 @ sk_D_1)
% 6.90/7.11          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 6.90/7.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['39', '40'])).
% 6.90/7.11  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('43', plain, ((v4_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('44', plain, ((v5_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('46', plain,
% 6.90/7.11      (![X0 : $i, X1 : $i]:
% 6.90/7.11         ((v2_struct_0 @ sk_A)
% 6.90/7.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (r2_hidden @ X1 @ sk_D_1)
% 6.90/7.11          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 6.90/7.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 6.90/7.11  thf('47', plain,
% 6.90/7.11      ((~ (m1_subset_1 @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           (u1_struct_0 @ sk_A))
% 6.90/7.11        | (r2_hidden @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           sk_D_1)
% 6.90/7.11        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 6.90/7.11        | (v2_struct_0 @ sk_A))),
% 6.90/7.11      inference('sup-', [status(thm)], ['38', '46'])).
% 6.90/7.11  thf('48', plain,
% 6.90/7.11      ((m1_subset_1 @ 
% 6.90/7.11        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11        (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('clc', [status(thm)], ['18', '19'])).
% 6.90/7.11  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('50', plain,
% 6.90/7.11      (((r2_hidden @ 
% 6.90/7.11         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11         sk_D_1)
% 6.90/7.11        | (v2_struct_0 @ sk_A))),
% 6.90/7.11      inference('demod', [status(thm)], ['47', '48', '49'])).
% 6.90/7.11  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('52', plain,
% 6.90/7.11      ((r2_hidden @ 
% 6.90/7.11        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11        sk_D_1)),
% 6.90/7.11      inference('clc', [status(thm)], ['50', '51'])).
% 6.90/7.11  thf('53', plain,
% 6.90/7.11      (((v2_struct_0 @ sk_A)
% 6.90/7.11        | (r2_hidden @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 6.90/7.11        | ~ (r2_orders_2 @ sk_A @ 
% 6.90/7.11             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11             sk_C))),
% 6.90/7.11      inference('demod', [status(thm)], ['31', '52'])).
% 6.90/7.11  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('55', plain,
% 6.90/7.11      ((~ (r2_orders_2 @ sk_A @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           sk_C)
% 6.90/7.11        | (r2_hidden @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 6.90/7.11      inference('clc', [status(thm)], ['53', '54'])).
% 6.90/7.11  thf('56', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('57', plain,
% 6.90/7.11      ((r2_hidden @ 
% 6.90/7.11        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 6.90/7.11      inference('clc', [status(thm)], ['36', '37'])).
% 6.90/7.11  thf('58', plain,
% 6.90/7.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('59', plain,
% 6.90/7.11      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 6.90/7.11          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 6.90/7.11          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 6.90/7.11          | (r2_orders_2 @ X11 @ X10 @ X13)
% 6.90/7.11          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 6.90/7.11          | ~ (l1_orders_2 @ X11)
% 6.90/7.11          | ~ (v5_orders_2 @ X11)
% 6.90/7.11          | ~ (v4_orders_2 @ X11)
% 6.90/7.11          | ~ (v3_orders_2 @ X11)
% 6.90/7.11          | (v2_struct_0 @ X11))),
% 6.90/7.11      inference('cnf', [status(esa)], [t57_orders_2])).
% 6.90/7.11  thf('60', plain,
% 6.90/7.11      (![X0 : $i, X1 : $i]:
% 6.90/7.11         ((v2_struct_0 @ sk_A)
% 6.90/7.11          | ~ (v3_orders_2 @ sk_A)
% 6.90/7.11          | ~ (v4_orders_2 @ sk_A)
% 6.90/7.11          | ~ (v5_orders_2 @ sk_A)
% 6.90/7.11          | ~ (l1_orders_2 @ sk_A)
% 6.90/7.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 6.90/7.11          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 6.90/7.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('sup-', [status(thm)], ['58', '59'])).
% 6.90/7.11  thf('61', plain, ((v3_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('62', plain, ((v4_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('65', plain,
% 6.90/7.11      (![X0 : $i, X1 : $i]:
% 6.90/7.11         ((v2_struct_0 @ sk_A)
% 6.90/7.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.11          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 6.90/7.11          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 6.90/7.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.11      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 6.90/7.11  thf('66', plain,
% 6.90/7.11      ((~ (m1_subset_1 @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           (u1_struct_0 @ sk_A))
% 6.90/7.11        | (r2_orders_2 @ sk_A @ 
% 6.90/7.11           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11           sk_B)
% 6.90/7.11        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 6.90/7.11        | (v2_struct_0 @ sk_A))),
% 6.90/7.11      inference('sup-', [status(thm)], ['57', '65'])).
% 6.90/7.11  thf('67', plain,
% 6.90/7.11      ((m1_subset_1 @ 
% 6.90/7.11        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11        (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('clc', [status(thm)], ['18', '19'])).
% 6.90/7.11  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('69', plain,
% 6.90/7.11      (((r2_orders_2 @ sk_A @ 
% 6.90/7.11         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11         sk_B)
% 6.90/7.11        | (v2_struct_0 @ sk_A))),
% 6.90/7.11      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.90/7.11  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 6.90/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.11  thf('71', plain,
% 6.90/7.11      ((r2_orders_2 @ sk_A @ 
% 6.90/7.11        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11        sk_B)),
% 6.90/7.11      inference('clc', [status(thm)], ['69', '70'])).
% 6.90/7.11  thf('72', plain,
% 6.90/7.11      ((m1_subset_1 @ 
% 6.90/7.11        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.11         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.11        (u1_struct_0 @ sk_A))),
% 6.90/7.11      inference('clc', [status(thm)], ['18', '19'])).
% 6.90/7.11  thf(t29_orders_2, axiom,
% 6.90/7.11    (![A:$i]:
% 6.90/7.11     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 6.90/7.11       ( ![B:$i]:
% 6.90/7.11         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11           ( ![C:$i]:
% 6.90/7.11             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11               ( ![D:$i]:
% 6.90/7.11                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.90/7.11                   ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 6.90/7.11                       ( r2_orders_2 @ A @ C @ D ) ) =>
% 6.90/7.11                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 6.90/7.11  thf('73', plain,
% 6.90/7.11      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 6.90/7.11         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 6.90/7.11          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 6.90/7.11          | (r2_orders_2 @ X7 @ X6 @ X8)
% 6.90/7.11          | ~ (r2_orders_2 @ X7 @ X9 @ X8)
% 6.90/7.11          | ~ (r2_orders_2 @ X7 @ X6 @ X9)
% 6.90/7.11          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 6.90/7.11          | ~ (l1_orders_2 @ X7)
% 6.90/7.12          | ~ (v5_orders_2 @ X7)
% 6.90/7.12          | ~ (v4_orders_2 @ X7))),
% 6.90/7.12      inference('cnf', [status(esa)], [t29_orders_2])).
% 6.90/7.12  thf('74', plain,
% 6.90/7.12      (![X0 : $i, X1 : $i]:
% 6.90/7.12         (~ (v4_orders_2 @ sk_A)
% 6.90/7.12          | ~ (v5_orders_2 @ sk_A)
% 6.90/7.12          | ~ (l1_orders_2 @ sk_A)
% 6.90/7.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.12          | ~ (r2_orders_2 @ sk_A @ 
% 6.90/7.12               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12                (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12               X0)
% 6.90/7.12          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 6.90/7.12          | (r2_orders_2 @ sk_A @ 
% 6.90/7.12             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12             X1)
% 6.90/7.12          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.12      inference('sup-', [status(thm)], ['72', '73'])).
% 6.90/7.12  thf('75', plain, ((v4_orders_2 @ sk_A)),
% 6.90/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.12  thf('76', plain, ((v5_orders_2 @ sk_A)),
% 6.90/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.12  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 6.90/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.12  thf('78', plain,
% 6.90/7.12      (![X0 : $i, X1 : $i]:
% 6.90/7.12         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.12          | ~ (r2_orders_2 @ sk_A @ 
% 6.90/7.12               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12                (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12               X0)
% 6.90/7.12          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 6.90/7.12          | (r2_orders_2 @ sk_A @ 
% 6.90/7.12             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12             X1)
% 6.90/7.12          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.12      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 6.90/7.12  thf('79', plain,
% 6.90/7.12      (![X0 : $i]:
% 6.90/7.12         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.12          | (r2_orders_2 @ sk_A @ 
% 6.90/7.12             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12             X0)
% 6.90/7.12          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 6.90/7.12          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 6.90/7.12      inference('sup-', [status(thm)], ['71', '78'])).
% 6.90/7.12  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.90/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.12  thf('81', plain,
% 6.90/7.12      (![X0 : $i]:
% 6.90/7.12         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.90/7.12          | (r2_orders_2 @ sk_A @ 
% 6.90/7.12             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12             X0)
% 6.90/7.12          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 6.90/7.12      inference('demod', [status(thm)], ['79', '80'])).
% 6.90/7.12  thf('82', plain,
% 6.90/7.12      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 6.90/7.12        | (r2_orders_2 @ sk_A @ 
% 6.90/7.12           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12           sk_C))),
% 6.90/7.12      inference('sup-', [status(thm)], ['56', '81'])).
% 6.90/7.12  thf('83', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 6.90/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.90/7.12  thf('84', plain,
% 6.90/7.12      ((r2_orders_2 @ sk_A @ 
% 6.90/7.12        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12        sk_C)),
% 6.90/7.12      inference('demod', [status(thm)], ['82', '83'])).
% 6.90/7.12  thf('85', plain,
% 6.90/7.12      ((r2_hidden @ 
% 6.90/7.12        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 6.90/7.12      inference('demod', [status(thm)], ['55', '84'])).
% 6.90/7.12  thf('86', plain,
% 6.90/7.12      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 6.90/7.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.12      inference('sup-', [status(thm)], ['13', '14'])).
% 6.90/7.12  thf('87', plain,
% 6.90/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.90/7.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 6.90/7.12          | (r1_tarski @ X2 @ X0)
% 6.90/7.12          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 6.90/7.12          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 6.90/7.12      inference('cnf', [status(esa)], [t7_subset_1])).
% 6.90/7.12  thf('88', plain,
% 6.90/7.12      (![X0 : $i]:
% 6.90/7.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.90/7.12          | ~ (r2_hidden @ 
% 6.90/7.12               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ X0 @ 
% 6.90/7.12                (u1_struct_0 @ sk_A)) @ 
% 6.90/7.12               (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 6.90/7.12          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 6.90/7.12      inference('sup-', [status(thm)], ['86', '87'])).
% 6.90/7.12  thf('89', plain,
% 6.90/7.12      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.12         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 6.90/7.12        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.12             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.90/7.12      inference('sup-', [status(thm)], ['85', '88'])).
% 6.90/7.12  thf('90', plain,
% 6.90/7.12      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.90/7.12      inference('sup-', [status(thm)], ['1', '11'])).
% 6.90/7.12  thf('91', plain,
% 6.90/7.12      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 6.90/7.12        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 6.90/7.12      inference('demod', [status(thm)], ['89', '90'])).
% 6.90/7.12  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 6.90/7.12  
% 6.90/7.12  % SZS output end Refutation
% 6.90/7.12  
% 6.90/7.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
