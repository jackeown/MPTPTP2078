%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fVYMgVbiVS

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:03 EST 2020

% Result     : Theorem 11.29s
% Output     : Refutation 11.29s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 639 expanded)
%              Number of leaves         :   24 ( 196 expanded)
%              Depth                    :   22
%              Number of atoms          : 1603 (14706 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_orders_2 @ X14 @ X13 @ X16 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k3_orders_2 @ X14 @ X15 @ X16 ) )
      | ( r2_orders_2 @ X14 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('73',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_orders_2 @ X4 @ X3 @ X5 )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t32_orders_2,axiom,(
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
                 => ( ( ( ( r2_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ C @ D ) )
                      | ( ( r1_orders_2 @ A @ B @ C )
                        & ( r2_orders_2 @ A @ C @ D ) ) )
                   => ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r2_orders_2 @ X10 @ X9 @ X11 )
      | ~ ( r2_orders_2 @ X10 @ X12 @ X11 )
      | ~ ( r1_orders_2 @ X10 @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t32_orders_2])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['56','89'])).

thf('91',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('99',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fVYMgVbiVS
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 11.29/11.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.29/11.48  % Solved by: fo/fo7.sh
% 11.29/11.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.29/11.48  % done 2600 iterations in 11.007s
% 11.29/11.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.29/11.48  % SZS output start Refutation
% 11.29/11.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 11.29/11.48  thf(sk_B_type, type, sk_B: $i).
% 11.29/11.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.29/11.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.29/11.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 11.29/11.48  thf(sk_A_type, type, sk_A: $i).
% 11.29/11.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 11.29/11.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 11.29/11.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 11.29/11.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 11.29/11.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.29/11.48  thf(sk_C_type, type, sk_C: $i).
% 11.29/11.48  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 11.29/11.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.29/11.48  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 11.29/11.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.29/11.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 11.29/11.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 11.29/11.48  thf(t64_orders_2, conjecture,
% 11.29/11.48    (![A:$i]:
% 11.29/11.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 11.29/11.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.29/11.48       ( ![B:$i]:
% 11.29/11.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48           ( ![C:$i]:
% 11.29/11.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48               ( ![D:$i]:
% 11.29/11.48                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.48                   ( ( r2_orders_2 @ A @ B @ C ) =>
% 11.29/11.48                     ( r1_tarski @
% 11.29/11.48                       ( k3_orders_2 @ A @ D @ B ) @ 
% 11.29/11.48                       ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 11.29/11.48  thf(zf_stmt_0, negated_conjecture,
% 11.29/11.48    (~( ![A:$i]:
% 11.29/11.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 11.29/11.48            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.29/11.48          ( ![B:$i]:
% 11.29/11.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48              ( ![C:$i]:
% 11.29/11.48                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48                  ( ![D:$i]:
% 11.29/11.48                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.48                      ( ( r2_orders_2 @ A @ B @ C ) =>
% 11.29/11.48                        ( r1_tarski @
% 11.29/11.48                          ( k3_orders_2 @ A @ D @ B ) @ 
% 11.29/11.48                          ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 11.29/11.48    inference('cnf.neg', [status(esa)], [t64_orders_2])).
% 11.29/11.48  thf('0', plain,
% 11.29/11.48      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('2', plain,
% 11.29/11.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf(dt_k3_orders_2, axiom,
% 11.29/11.48    (![A:$i,B:$i,C:$i]:
% 11.29/11.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 11.29/11.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 11.29/11.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 11.29/11.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.48       ( m1_subset_1 @
% 11.29/11.48         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 11.29/11.48  thf('3', plain,
% 11.29/11.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 11.29/11.48          | ~ (l1_orders_2 @ X7)
% 11.29/11.48          | ~ (v5_orders_2 @ X7)
% 11.29/11.48          | ~ (v4_orders_2 @ X7)
% 11.29/11.48          | ~ (v3_orders_2 @ X7)
% 11.29/11.48          | (v2_struct_0 @ X7)
% 11.29/11.48          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 11.29/11.48          | (m1_subset_1 @ (k3_orders_2 @ X7 @ X6 @ X8) @ 
% 11.29/11.48             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 11.29/11.48      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 11.29/11.48  thf('4', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 11.29/11.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (v2_struct_0 @ sk_A)
% 11.29/11.48          | ~ (v3_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v4_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v5_orders_2 @ sk_A)
% 11.29/11.48          | ~ (l1_orders_2 @ sk_A))),
% 11.29/11.48      inference('sup-', [status(thm)], ['2', '3'])).
% 11.29/11.48  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('6', plain, ((v4_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('9', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 11.29/11.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (v2_struct_0 @ sk_A))),
% 11.29/11.48      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 11.29/11.48  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('11', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 11.29/11.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 11.29/11.48      inference('clc', [status(thm)], ['9', '10'])).
% 11.29/11.48  thf('12', plain,
% 11.29/11.48      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['1', '11'])).
% 11.29/11.48  thf('13', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('14', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 11.29/11.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 11.29/11.48      inference('clc', [status(thm)], ['9', '10'])).
% 11.29/11.48  thf('15', plain,
% 11.29/11.48      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['13', '14'])).
% 11.29/11.48  thf(t7_subset_1, axiom,
% 11.29/11.48    (![A:$i,B:$i]:
% 11.29/11.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.29/11.48       ( ![C:$i]:
% 11.29/11.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 11.29/11.48           ( ( ![D:$i]:
% 11.29/11.48               ( ( m1_subset_1 @ D @ A ) =>
% 11.29/11.48                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 11.29/11.48             ( r1_tarski @ B @ C ) ) ) ) ))).
% 11.29/11.48  thf('16', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 11.29/11.48          | (r1_tarski @ X2 @ X0)
% 11.29/11.48          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 11.29/11.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 11.29/11.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 11.29/11.48  thf('17', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.29/11.48          | (m1_subset_1 @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ X0 @ 
% 11.29/11.48              (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['15', '16'])).
% 11.29/11.48  thf('18', plain,
% 11.29/11.48      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 11.29/11.48        | (m1_subset_1 @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['12', '17'])).
% 11.29/11.48  thf('19', plain,
% 11.29/11.48      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('20', plain,
% 11.29/11.48      ((m1_subset_1 @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('clc', [status(thm)], ['18', '19'])).
% 11.29/11.48  thf('21', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('22', plain,
% 11.29/11.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf(t57_orders_2, axiom,
% 11.29/11.48    (![A:$i]:
% 11.29/11.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 11.29/11.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.29/11.48       ( ![B:$i]:
% 11.29/11.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48           ( ![C:$i]:
% 11.29/11.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48               ( ![D:$i]:
% 11.29/11.48                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.48                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 11.29/11.48                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 11.29/11.48  thf('23', plain,
% 11.29/11.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 11.29/11.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 11.29/11.48          | ~ (r2_orders_2 @ X14 @ X13 @ X16)
% 11.29/11.48          | ~ (r2_hidden @ X13 @ X15)
% 11.29/11.48          | (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 11.29/11.48          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 11.29/11.48          | ~ (l1_orders_2 @ X14)
% 11.29/11.48          | ~ (v5_orders_2 @ X14)
% 11.29/11.48          | ~ (v4_orders_2 @ X14)
% 11.29/11.48          | ~ (v3_orders_2 @ X14)
% 11.29/11.48          | (v2_struct_0 @ X14))),
% 11.29/11.48      inference('cnf', [status(esa)], [t57_orders_2])).
% 11.29/11.48  thf('24', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i]:
% 11.29/11.48         ((v2_struct_0 @ sk_A)
% 11.29/11.48          | ~ (v3_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v4_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v5_orders_2 @ sk_A)
% 11.29/11.48          | ~ (l1_orders_2 @ sk_A)
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 11.29/11.48          | ~ (r2_hidden @ X1 @ sk_D_1)
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 11.29/11.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['22', '23'])).
% 11.29/11.48  thf('25', plain, ((v3_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('27', plain, ((v5_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('29', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i]:
% 11.29/11.48         ((v2_struct_0 @ sk_A)
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 11.29/11.48          | ~ (r2_hidden @ X1 @ sk_D_1)
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 11.29/11.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 11.29/11.48  thf('30', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C)
% 11.29/11.48          | ~ (r2_hidden @ X0 @ sk_D_1)
% 11.29/11.48          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 11.29/11.48          | (v2_struct_0 @ sk_A))),
% 11.29/11.48      inference('sup-', [status(thm)], ['21', '29'])).
% 11.29/11.48  thf('31', plain,
% 11.29/11.48      (((v2_struct_0 @ sk_A)
% 11.29/11.48        | (r2_hidden @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 11.29/11.48        | ~ (r2_hidden @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             sk_D_1)
% 11.29/11.48        | ~ (r2_orders_2 @ sk_A @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             sk_C))),
% 11.29/11.48      inference('sup-', [status(thm)], ['20', '30'])).
% 11.29/11.48  thf('32', plain,
% 11.29/11.48      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['1', '11'])).
% 11.29/11.48  thf('33', plain,
% 11.29/11.48      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['13', '14'])).
% 11.29/11.48  thf('34', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 11.29/11.48          | (r1_tarski @ X2 @ X0)
% 11.29/11.48          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 11.29/11.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 11.29/11.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 11.29/11.48  thf('35', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.29/11.48          | (r2_hidden @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ X0 @ 
% 11.29/11.48              (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             X0)
% 11.29/11.48          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['33', '34'])).
% 11.29/11.48  thf('36', plain,
% 11.29/11.48      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 11.29/11.48        | (r2_hidden @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['32', '35'])).
% 11.29/11.48  thf('37', plain,
% 11.29/11.48      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('38', plain,
% 11.29/11.48      ((r2_hidden @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 11.29/11.48      inference('clc', [status(thm)], ['36', '37'])).
% 11.29/11.48  thf('39', plain,
% 11.29/11.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('40', plain,
% 11.29/11.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 11.29/11.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 11.29/11.48          | ~ (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 11.29/11.48          | (r2_hidden @ X13 @ X15)
% 11.29/11.48          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 11.29/11.48          | ~ (l1_orders_2 @ X14)
% 11.29/11.48          | ~ (v5_orders_2 @ X14)
% 11.29/11.48          | ~ (v4_orders_2 @ X14)
% 11.29/11.48          | ~ (v3_orders_2 @ X14)
% 11.29/11.48          | (v2_struct_0 @ X14))),
% 11.29/11.48      inference('cnf', [status(esa)], [t57_orders_2])).
% 11.29/11.48  thf('41', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i]:
% 11.29/11.48         ((v2_struct_0 @ sk_A)
% 11.29/11.48          | ~ (v3_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v4_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v5_orders_2 @ sk_A)
% 11.29/11.48          | ~ (l1_orders_2 @ sk_A)
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r2_hidden @ X1 @ sk_D_1)
% 11.29/11.48          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 11.29/11.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['39', '40'])).
% 11.29/11.48  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('43', plain, ((v4_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('44', plain, ((v5_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('46', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i]:
% 11.29/11.48         ((v2_struct_0 @ sk_A)
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r2_hidden @ X1 @ sk_D_1)
% 11.29/11.48          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 11.29/11.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 11.29/11.48  thf('47', plain,
% 11.29/11.48      ((~ (m1_subset_1 @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           (u1_struct_0 @ sk_A))
% 11.29/11.48        | (r2_hidden @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           sk_D_1)
% 11.29/11.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 11.29/11.48        | (v2_struct_0 @ sk_A))),
% 11.29/11.48      inference('sup-', [status(thm)], ['38', '46'])).
% 11.29/11.48  thf('48', plain,
% 11.29/11.48      ((m1_subset_1 @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('clc', [status(thm)], ['18', '19'])).
% 11.29/11.48  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('50', plain,
% 11.29/11.48      (((r2_hidden @ 
% 11.29/11.48         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48         sk_D_1)
% 11.29/11.48        | (v2_struct_0 @ sk_A))),
% 11.29/11.48      inference('demod', [status(thm)], ['47', '48', '49'])).
% 11.29/11.48  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('52', plain,
% 11.29/11.48      ((r2_hidden @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        sk_D_1)),
% 11.29/11.48      inference('clc', [status(thm)], ['50', '51'])).
% 11.29/11.48  thf('53', plain,
% 11.29/11.48      (((v2_struct_0 @ sk_A)
% 11.29/11.48        | (r2_hidden @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 11.29/11.48        | ~ (r2_orders_2 @ sk_A @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             sk_C))),
% 11.29/11.48      inference('demod', [status(thm)], ['31', '52'])).
% 11.29/11.48  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('55', plain,
% 11.29/11.48      ((~ (r2_orders_2 @ sk_A @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           sk_C)
% 11.29/11.48        | (r2_hidden @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 11.29/11.48      inference('clc', [status(thm)], ['53', '54'])).
% 11.29/11.48  thf('56', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('57', plain,
% 11.29/11.48      ((r2_hidden @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 11.29/11.48      inference('clc', [status(thm)], ['36', '37'])).
% 11.29/11.48  thf('58', plain,
% 11.29/11.48      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('59', plain,
% 11.29/11.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 11.29/11.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 11.29/11.48          | ~ (r2_hidden @ X13 @ (k3_orders_2 @ X14 @ X15 @ X16))
% 11.29/11.48          | (r2_orders_2 @ X14 @ X13 @ X16)
% 11.29/11.48          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 11.29/11.48          | ~ (l1_orders_2 @ X14)
% 11.29/11.48          | ~ (v5_orders_2 @ X14)
% 11.29/11.48          | ~ (v4_orders_2 @ X14)
% 11.29/11.48          | ~ (v3_orders_2 @ X14)
% 11.29/11.48          | (v2_struct_0 @ X14))),
% 11.29/11.48      inference('cnf', [status(esa)], [t57_orders_2])).
% 11.29/11.48  thf('60', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i]:
% 11.29/11.48         ((v2_struct_0 @ sk_A)
% 11.29/11.48          | ~ (v3_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v4_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v5_orders_2 @ sk_A)
% 11.29/11.48          | ~ (l1_orders_2 @ sk_A)
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 11.29/11.48          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 11.29/11.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['58', '59'])).
% 11.29/11.48  thf('61', plain, ((v3_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('62', plain, ((v4_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('65', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i]:
% 11.29/11.48         ((v2_struct_0 @ sk_A)
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 11.29/11.48          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 11.29/11.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 11.29/11.48  thf('66', plain,
% 11.29/11.48      ((~ (m1_subset_1 @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           (u1_struct_0 @ sk_A))
% 11.29/11.48        | (r2_orders_2 @ sk_A @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           sk_B)
% 11.29/11.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 11.29/11.48        | (v2_struct_0 @ sk_A))),
% 11.29/11.48      inference('sup-', [status(thm)], ['57', '65'])).
% 11.29/11.48  thf('67', plain,
% 11.29/11.48      ((m1_subset_1 @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('clc', [status(thm)], ['18', '19'])).
% 11.29/11.48  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('69', plain,
% 11.29/11.48      (((r2_orders_2 @ sk_A @ 
% 11.29/11.48         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48         sk_B)
% 11.29/11.48        | (v2_struct_0 @ sk_A))),
% 11.29/11.48      inference('demod', [status(thm)], ['66', '67', '68'])).
% 11.29/11.48  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('71', plain,
% 11.29/11.48      ((r2_orders_2 @ sk_A @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        sk_B)),
% 11.29/11.48      inference('clc', [status(thm)], ['69', '70'])).
% 11.29/11.48  thf('72', plain,
% 11.29/11.48      ((m1_subset_1 @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('clc', [status(thm)], ['18', '19'])).
% 11.29/11.48  thf(d10_orders_2, axiom,
% 11.29/11.48    (![A:$i]:
% 11.29/11.48     ( ( l1_orders_2 @ A ) =>
% 11.29/11.48       ( ![B:$i]:
% 11.29/11.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48           ( ![C:$i]:
% 11.29/11.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 11.29/11.48                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 11.29/11.48  thf('73', plain,
% 11.29/11.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 11.29/11.48          | ~ (r2_orders_2 @ X4 @ X3 @ X5)
% 11.29/11.48          | (r1_orders_2 @ X4 @ X3 @ X5)
% 11.29/11.48          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 11.29/11.48          | ~ (l1_orders_2 @ X4))),
% 11.29/11.48      inference('cnf', [status(esa)], [d10_orders_2])).
% 11.29/11.48  thf('74', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (l1_orders_2 @ sk_A)
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r1_orders_2 @ sk_A @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             X0)
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ 
% 11.29/11.48               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48                (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48               X0))),
% 11.29/11.48      inference('sup-', [status(thm)], ['72', '73'])).
% 11.29/11.48  thf('75', plain, ((l1_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('76', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r1_orders_2 @ sk_A @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             X0)
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ 
% 11.29/11.48               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48                (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48               X0))),
% 11.29/11.48      inference('demod', [status(thm)], ['74', '75'])).
% 11.29/11.48  thf('77', plain,
% 11.29/11.48      (((r1_orders_2 @ sk_A @ 
% 11.29/11.48         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48         sk_B)
% 11.29/11.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['71', '76'])).
% 11.29/11.48  thf('78', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('79', plain,
% 11.29/11.48      ((r1_orders_2 @ sk_A @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        sk_B)),
% 11.29/11.48      inference('demod', [status(thm)], ['77', '78'])).
% 11.29/11.48  thf('80', plain,
% 11.29/11.48      ((m1_subset_1 @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('clc', [status(thm)], ['18', '19'])).
% 11.29/11.48  thf(t32_orders_2, axiom,
% 11.29/11.48    (![A:$i]:
% 11.29/11.48     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.29/11.48       ( ![B:$i]:
% 11.29/11.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48           ( ![C:$i]:
% 11.29/11.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48               ( ![D:$i]:
% 11.29/11.48                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.29/11.48                   ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 11.29/11.48                         ( r1_orders_2 @ A @ C @ D ) ) | 
% 11.29/11.48                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 11.29/11.48                         ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 11.29/11.48                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 11.29/11.48  thf('81', plain,
% 11.29/11.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 11.29/11.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 11.29/11.48          | (r2_orders_2 @ X10 @ X9 @ X11)
% 11.29/11.48          | ~ (r2_orders_2 @ X10 @ X12 @ X11)
% 11.29/11.48          | ~ (r1_orders_2 @ X10 @ X9 @ X12)
% 11.29/11.48          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 11.29/11.48          | ~ (l1_orders_2 @ X10)
% 11.29/11.48          | ~ (v5_orders_2 @ X10)
% 11.29/11.48          | ~ (v4_orders_2 @ X10))),
% 11.29/11.48      inference('cnf', [status(esa)], [t32_orders_2])).
% 11.29/11.48  thf('82', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i]:
% 11.29/11.48         (~ (v4_orders_2 @ sk_A)
% 11.29/11.48          | ~ (v5_orders_2 @ sk_A)
% 11.29/11.48          | ~ (l1_orders_2 @ sk_A)
% 11.29/11.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | ~ (r1_orders_2 @ sk_A @ 
% 11.29/11.48               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48                (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48               X0)
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 11.29/11.48          | (r2_orders_2 @ sk_A @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             X1)
% 11.29/11.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['80', '81'])).
% 11.29/11.48  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('86', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | ~ (r1_orders_2 @ sk_A @ 
% 11.29/11.48               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48                (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48               X0)
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 11.29/11.48          | (r2_orders_2 @ sk_A @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             X1)
% 11.29/11.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 11.29/11.48  thf('87', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r2_orders_2 @ sk_A @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             X0)
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 11.29/11.48          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['79', '86'])).
% 11.29/11.48  thf('88', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('89', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.29/11.48          | (r2_orders_2 @ sk_A @ 
% 11.29/11.48             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48              (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48             X0)
% 11.29/11.48          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 11.29/11.48      inference('demod', [status(thm)], ['87', '88'])).
% 11.29/11.48  thf('90', plain,
% 11.29/11.48      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 11.29/11.48        | (r2_orders_2 @ sk_A @ 
% 11.29/11.48           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48            (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48           sk_C))),
% 11.29/11.48      inference('sup-', [status(thm)], ['56', '89'])).
% 11.29/11.48  thf('91', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 11.29/11.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.48  thf('92', plain,
% 11.29/11.48      ((r2_orders_2 @ sk_A @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        sk_C)),
% 11.29/11.48      inference('demod', [status(thm)], ['90', '91'])).
% 11.29/11.48  thf('93', plain,
% 11.29/11.48      ((r2_hidden @ 
% 11.29/11.48        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 11.29/11.48      inference('demod', [status(thm)], ['55', '92'])).
% 11.29/11.48  thf('94', plain,
% 11.29/11.48      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ 
% 11.29/11.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['13', '14'])).
% 11.29/11.48  thf('95', plain,
% 11.29/11.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 11.29/11.48          | (r1_tarski @ X2 @ X0)
% 11.29/11.48          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 11.29/11.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 11.29/11.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 11.29/11.48  thf('96', plain,
% 11.29/11.48      (![X0 : $i]:
% 11.29/11.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.29/11.48          | ~ (r2_hidden @ 
% 11.29/11.48               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C) @ X0 @ 
% 11.29/11.48                (u1_struct_0 @ sk_A)) @ 
% 11.29/11.48               (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 11.29/11.48          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['94', '95'])).
% 11.29/11.48  thf('97', plain,
% 11.29/11.48      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))
% 11.29/11.48        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 11.29/11.48      inference('sup-', [status(thm)], ['93', '96'])).
% 11.29/11.48  thf('98', plain,
% 11.29/11.48      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.48      inference('sup-', [status(thm)], ['1', '11'])).
% 11.29/11.48  thf('99', plain,
% 11.29/11.48      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 11.29/11.48        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_C))),
% 11.29/11.48      inference('demod', [status(thm)], ['97', '98'])).
% 11.29/11.48  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 11.29/11.48  
% 11.29/11.48  % SZS output end Refutation
% 11.29/11.48  
% 11.29/11.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
