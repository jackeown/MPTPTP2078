%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uVnqHa8rRz

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:04 EST 2020

% Result     : Theorem 3.05s
% Output     : Refutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 541 expanded)
%              Number of leaves         :   23 ( 168 expanded)
%              Depth                    :   27
%              Number of atoms          : 1607 (12028 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
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
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 )
    | ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('42',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','69'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('79',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','82'])).

thf('84',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ sk_D_1 ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['47','92'])).

thf('94',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('95',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
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

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r2_orders_2 @ sk_A @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','93','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('113',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('117',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['0','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uVnqHa8rRz
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:28:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.05/3.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.05/3.25  % Solved by: fo/fo7.sh
% 3.05/3.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.05/3.25  % done 988 iterations in 2.806s
% 3.05/3.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.05/3.25  % SZS output start Refutation
% 3.05/3.25  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 3.05/3.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.05/3.25  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 3.05/3.25  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 3.05/3.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.05/3.25  thf(sk_A_type, type, sk_A: $i).
% 3.05/3.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.05/3.25  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 3.05/3.25  thf(sk_B_type, type, sk_B: $i).
% 3.05/3.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.05/3.25  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.05/3.25  thf(sk_D_1_type, type, sk_D_1: $i).
% 3.05/3.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.05/3.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.05/3.25  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 3.05/3.25  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 3.05/3.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.05/3.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.05/3.25  thf(t65_orders_2, conjecture,
% 3.05/3.25    (![A:$i]:
% 3.05/3.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.05/3.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.05/3.25       ( ![B:$i]:
% 3.05/3.25         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.05/3.25           ( ![C:$i]:
% 3.05/3.25             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.05/3.25               ( ![D:$i]:
% 3.05/3.25                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.05/3.25                   ( ( r1_tarski @ C @ D ) =>
% 3.05/3.25                     ( r1_tarski @
% 3.05/3.25                       ( k3_orders_2 @ A @ C @ B ) @ 
% 3.05/3.25                       ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 3.05/3.25  thf(zf_stmt_0, negated_conjecture,
% 3.05/3.25    (~( ![A:$i]:
% 3.05/3.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.05/3.25            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.05/3.25          ( ![B:$i]:
% 3.05/3.25            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.05/3.25              ( ![C:$i]:
% 3.05/3.25                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.05/3.25                  ( ![D:$i]:
% 3.05/3.25                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.05/3.25                      ( ( r1_tarski @ C @ D ) =>
% 3.05/3.25                        ( r1_tarski @
% 3.05/3.25                          ( k3_orders_2 @ A @ C @ B ) @ 
% 3.05/3.25                          ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 3.05/3.25    inference('cnf.neg', [status(esa)], [t65_orders_2])).
% 3.05/3.25  thf('0', plain,
% 3.05/3.25      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.25          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('2', plain,
% 3.05/3.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf(dt_k3_orders_2, axiom,
% 3.05/3.25    (![A:$i,B:$i,C:$i]:
% 3.05/3.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.05/3.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 3.05/3.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 3.05/3.25         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 3.05/3.25       ( m1_subset_1 @
% 3.05/3.25         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.05/3.25  thf('3', plain,
% 3.05/3.25      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.05/3.25         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 3.05/3.25          | ~ (l1_orders_2 @ X8)
% 3.05/3.25          | ~ (v5_orders_2 @ X8)
% 3.05/3.25          | ~ (v4_orders_2 @ X8)
% 3.05/3.25          | ~ (v3_orders_2 @ X8)
% 3.05/3.25          | (v2_struct_0 @ X8)
% 3.05/3.25          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 3.05/3.25          | (m1_subset_1 @ (k3_orders_2 @ X8 @ X7 @ X9) @ 
% 3.05/3.25             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 3.05/3.25      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 3.05/3.25  thf('4', plain,
% 3.05/3.25      (![X0 : $i]:
% 3.05/3.25         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 3.05/3.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.25          | (v2_struct_0 @ sk_A)
% 3.05/3.25          | ~ (v3_orders_2 @ sk_A)
% 3.05/3.25          | ~ (v4_orders_2 @ sk_A)
% 3.05/3.25          | ~ (v5_orders_2 @ sk_A)
% 3.05/3.25          | ~ (l1_orders_2 @ sk_A))),
% 3.05/3.25      inference('sup-', [status(thm)], ['2', '3'])).
% 3.05/3.25  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('6', plain, ((v4_orders_2 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('9', plain,
% 3.05/3.25      (![X0 : $i]:
% 3.05/3.25         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 3.05/3.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.25          | (v2_struct_0 @ sk_A))),
% 3.05/3.25      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 3.05/3.25  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('11', plain,
% 3.05/3.25      (![X0 : $i]:
% 3.05/3.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.25          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0) @ 
% 3.05/3.25             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.05/3.25      inference('clc', [status(thm)], ['9', '10'])).
% 3.05/3.25  thf('12', plain,
% 3.05/3.25      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.25      inference('sup-', [status(thm)], ['1', '11'])).
% 3.05/3.25  thf('13', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('14', plain,
% 3.05/3.25      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('15', plain,
% 3.05/3.25      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.05/3.25         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 3.05/3.25          | ~ (l1_orders_2 @ X8)
% 3.05/3.25          | ~ (v5_orders_2 @ X8)
% 3.05/3.25          | ~ (v4_orders_2 @ X8)
% 3.05/3.25          | ~ (v3_orders_2 @ X8)
% 3.05/3.25          | (v2_struct_0 @ X8)
% 3.05/3.25          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 3.05/3.25          | (m1_subset_1 @ (k3_orders_2 @ X8 @ X7 @ X9) @ 
% 3.05/3.25             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 3.05/3.25      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 3.05/3.25  thf('16', plain,
% 3.05/3.25      (![X0 : $i]:
% 3.05/3.25         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 3.05/3.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.25          | (v2_struct_0 @ sk_A)
% 3.05/3.25          | ~ (v3_orders_2 @ sk_A)
% 3.05/3.25          | ~ (v4_orders_2 @ sk_A)
% 3.05/3.25          | ~ (v5_orders_2 @ sk_A)
% 3.05/3.25          | ~ (l1_orders_2 @ sk_A))),
% 3.05/3.25      inference('sup-', [status(thm)], ['14', '15'])).
% 3.05/3.25  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('18', plain, ((v4_orders_2 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 3.05/3.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.25  thf('21', plain,
% 3.05/3.25      (![X0 : $i]:
% 3.05/3.25         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 3.05/3.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | (v2_struct_0 @ sk_A))),
% 3.05/3.26      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 3.05/3.26  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('23', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0) @ 
% 3.05/3.26             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.05/3.26      inference('clc', [status(thm)], ['21', '22'])).
% 3.05/3.26  thf('24', plain,
% 3.05/3.26      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['13', '23'])).
% 3.05/3.26  thf(t7_subset_1, axiom,
% 3.05/3.26    (![A:$i,B:$i]:
% 3.05/3.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.05/3.26       ( ![C:$i]:
% 3.05/3.26         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.05/3.26           ( ( ![D:$i]:
% 3.05/3.26               ( ( m1_subset_1 @ D @ A ) =>
% 3.05/3.26                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 3.05/3.26             ( r1_tarski @ B @ C ) ) ) ) ))).
% 3.05/3.26  thf('25', plain,
% 3.05/3.26      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.05/3.26          | (r1_tarski @ X6 @ X4)
% 3.05/3.26          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ X5)
% 3.05/3.26          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.05/3.26      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.05/3.26  thf('26', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.26          | (m1_subset_1 @ 
% 3.05/3.26             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 3.05/3.26              (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26             (u1_struct_0 @ sk_A))
% 3.05/3.26          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['24', '25'])).
% 3.05/3.26  thf('27', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.05/3.26        | (m1_subset_1 @ 
% 3.05/3.26           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['12', '26'])).
% 3.05/3.26  thf('28', plain,
% 3.05/3.26      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('29', plain,
% 3.05/3.26      ((m1_subset_1 @ 
% 3.05/3.26        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26        (u1_struct_0 @ sk_A))),
% 3.05/3.26      inference('clc', [status(thm)], ['27', '28'])).
% 3.05/3.26  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('31', plain,
% 3.05/3.26      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf(t57_orders_2, axiom,
% 3.05/3.26    (![A:$i]:
% 3.05/3.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.05/3.26         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.05/3.26       ( ![B:$i]:
% 3.05/3.26         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.05/3.26           ( ![C:$i]:
% 3.05/3.26             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.05/3.26               ( ![D:$i]:
% 3.05/3.26                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.05/3.26                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 3.05/3.26                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 3.05/3.26  thf('32', plain,
% 3.05/3.26      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 3.05/3.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 3.05/3.26          | ~ (r2_orders_2 @ X11 @ X10 @ X13)
% 3.05/3.26          | ~ (r2_hidden @ X10 @ X12)
% 3.05/3.26          | (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 3.05/3.26          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 3.05/3.26          | ~ (l1_orders_2 @ X11)
% 3.05/3.26          | ~ (v5_orders_2 @ X11)
% 3.05/3.26          | ~ (v4_orders_2 @ X11)
% 3.05/3.26          | ~ (v3_orders_2 @ X11)
% 3.05/3.26          | (v2_struct_0 @ X11))),
% 3.05/3.26      inference('cnf', [status(esa)], [t57_orders_2])).
% 3.05/3.26  thf('33', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i]:
% 3.05/3.26         ((v2_struct_0 @ sk_A)
% 3.05/3.26          | ~ (v3_orders_2 @ sk_A)
% 3.05/3.26          | ~ (v4_orders_2 @ sk_A)
% 3.05/3.26          | ~ (v5_orders_2 @ sk_A)
% 3.05/3.26          | ~ (l1_orders_2 @ sk_A)
% 3.05/3.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 3.05/3.26          | ~ (r2_hidden @ X1 @ sk_D_1)
% 3.05/3.26          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 3.05/3.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['31', '32'])).
% 3.05/3.26  thf('34', plain, ((v3_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('35', plain, ((v4_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('36', plain, ((v5_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('38', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i]:
% 3.05/3.26         ((v2_struct_0 @ sk_A)
% 3.05/3.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ X0))
% 3.05/3.26          | ~ (r2_hidden @ X1 @ sk_D_1)
% 3.05/3.26          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 3.05/3.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 3.05/3.26  thf('39', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 3.05/3.26          | ~ (r2_hidden @ X0 @ sk_D_1)
% 3.05/3.26          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.05/3.26          | (v2_struct_0 @ sk_A))),
% 3.05/3.26      inference('sup-', [status(thm)], ['30', '38'])).
% 3.05/3.26  thf('40', plain,
% 3.05/3.26      (((v2_struct_0 @ sk_A)
% 3.05/3.26        | (r2_hidden @ 
% 3.05/3.26           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.05/3.26        | ~ (r2_hidden @ 
% 3.05/3.26             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26             sk_D_1)
% 3.05/3.26        | ~ (r2_orders_2 @ sk_A @ 
% 3.05/3.26             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26              (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26             sk_B))),
% 3.05/3.26      inference('sup-', [status(thm)], ['29', '39'])).
% 3.05/3.26  thf('41', plain,
% 3.05/3.26      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['1', '11'])).
% 3.05/3.26  thf('42', plain,
% 3.05/3.26      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['13', '23'])).
% 3.05/3.26  thf('43', plain,
% 3.05/3.26      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.05/3.26          | (r1_tarski @ X6 @ X4)
% 3.05/3.26          | (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 3.05/3.26          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.05/3.26      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.05/3.26  thf('44', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.26          | (r2_hidden @ 
% 3.05/3.26             (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 3.05/3.26              (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26             X0)
% 3.05/3.26          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['42', '43'])).
% 3.05/3.26  thf('45', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.05/3.26        | (r2_hidden @ 
% 3.05/3.26           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['41', '44'])).
% 3.05/3.26  thf('46', plain,
% 3.05/3.26      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26          (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('47', plain,
% 3.05/3.26      ((r2_hidden @ 
% 3.05/3.26        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26        (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 3.05/3.26      inference('clc', [status(thm)], ['45', '46'])).
% 3.05/3.26  thf(d3_tarski, axiom,
% 3.05/3.26    (![A:$i,B:$i]:
% 3.05/3.26     ( ( r1_tarski @ A @ B ) <=>
% 3.05/3.26       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.05/3.26  thf('48', plain,
% 3.05/3.26      (![X1 : $i, X3 : $i]:
% 3.05/3.26         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.05/3.26      inference('cnf', [status(esa)], [d3_tarski])).
% 3.05/3.26  thf('49', plain,
% 3.05/3.26      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['1', '11'])).
% 3.05/3.26  thf('50', plain,
% 3.05/3.26      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('51', plain,
% 3.05/3.26      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.05/3.26          | (r1_tarski @ X6 @ X4)
% 3.05/3.26          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ X5)
% 3.05/3.26          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.05/3.26      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.05/3.26  thf('52', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.26          | (m1_subset_1 @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26             (u1_struct_0 @ sk_A))
% 3.05/3.26          | (r1_tarski @ X0 @ sk_C_1))),
% 3.05/3.26      inference('sup-', [status(thm)], ['50', '51'])).
% 3.05/3.26  thf('53', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | (m1_subset_1 @ 
% 3.05/3.26           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26            (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['49', '52'])).
% 3.05/3.26  thf('54', plain,
% 3.05/3.26      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['1', '11'])).
% 3.05/3.26  thf('55', plain,
% 3.05/3.26      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('56', plain,
% 3.05/3.26      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.05/3.26          | (r1_tarski @ X6 @ X4)
% 3.05/3.26          | (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 3.05/3.26          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.05/3.26      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.05/3.26  thf('57', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.26          | (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.05/3.26          | (r1_tarski @ X0 @ sk_C_1))),
% 3.05/3.26      inference('sup-', [status(thm)], ['55', '56'])).
% 3.05/3.26  thf('58', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | (r2_hidden @ 
% 3.05/3.26           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26            (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['54', '57'])).
% 3.05/3.26  thf('59', plain,
% 3.05/3.26      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('60', plain,
% 3.05/3.26      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 3.05/3.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 3.05/3.26          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 3.05/3.26          | (r2_hidden @ X10 @ X12)
% 3.05/3.26          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 3.05/3.26          | ~ (l1_orders_2 @ X11)
% 3.05/3.26          | ~ (v5_orders_2 @ X11)
% 3.05/3.26          | ~ (v4_orders_2 @ X11)
% 3.05/3.26          | ~ (v3_orders_2 @ X11)
% 3.05/3.26          | (v2_struct_0 @ X11))),
% 3.05/3.26      inference('cnf', [status(esa)], [t57_orders_2])).
% 3.05/3.26  thf('61', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i]:
% 3.05/3.26         ((v2_struct_0 @ sk_A)
% 3.05/3.26          | ~ (v3_orders_2 @ sk_A)
% 3.05/3.26          | ~ (v4_orders_2 @ sk_A)
% 3.05/3.26          | ~ (v5_orders_2 @ sk_A)
% 3.05/3.26          | ~ (l1_orders_2 @ sk_A)
% 3.05/3.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | (r2_hidden @ X1 @ sk_C_1)
% 3.05/3.26          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 3.05/3.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['59', '60'])).
% 3.05/3.26  thf('62', plain, ((v3_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('63', plain, ((v4_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('64', plain, ((v5_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('66', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i]:
% 3.05/3.26         ((v2_struct_0 @ sk_A)
% 3.05/3.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | (r2_hidden @ X1 @ sk_C_1)
% 3.05/3.26          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 3.05/3.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 3.05/3.26  thf('67', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | ~ (m1_subset_1 @ 
% 3.05/3.26             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26              (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26             (u1_struct_0 @ sk_A))
% 3.05/3.26        | (r2_hidden @ 
% 3.05/3.26           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26            (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           sk_C_1)
% 3.05/3.26        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.05/3.26        | (v2_struct_0 @ sk_A))),
% 3.05/3.26      inference('sup-', [status(thm)], ['58', '66'])).
% 3.05/3.26  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('69', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | ~ (m1_subset_1 @ 
% 3.05/3.26             (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26              (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26             (u1_struct_0 @ sk_A))
% 3.05/3.26        | (r2_hidden @ 
% 3.05/3.26           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26            (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           sk_C_1)
% 3.05/3.26        | (v2_struct_0 @ sk_A))),
% 3.05/3.26      inference('demod', [status(thm)], ['67', '68'])).
% 3.05/3.26  thf('70', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | (v2_struct_0 @ sk_A)
% 3.05/3.26        | (r2_hidden @ 
% 3.05/3.26           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26            (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           sk_C_1)
% 3.05/3.26        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1))),
% 3.05/3.26      inference('sup-', [status(thm)], ['53', '69'])).
% 3.05/3.26  thf('71', plain,
% 3.05/3.26      (((r2_hidden @ 
% 3.05/3.26         (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26          (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26         sk_C_1)
% 3.05/3.26        | (v2_struct_0 @ sk_A)
% 3.05/3.26        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1))),
% 3.05/3.26      inference('simplify', [status(thm)], ['70'])).
% 3.05/3.26  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('73', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | (r2_hidden @ 
% 3.05/3.26           (sk_D @ sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26            (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           sk_C_1))),
% 3.05/3.26      inference('clc', [status(thm)], ['71', '72'])).
% 3.05/3.26  thf('74', plain,
% 3.05/3.26      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('75', plain,
% 3.05/3.26      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.05/3.26          | (r1_tarski @ X6 @ X4)
% 3.05/3.26          | ~ (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X4)
% 3.05/3.26          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.05/3.26      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.05/3.26  thf('76', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.26          | ~ (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_C_1)
% 3.05/3.26          | (r1_tarski @ X0 @ sk_C_1))),
% 3.05/3.26      inference('sup-', [status(thm)], ['74', '75'])).
% 3.05/3.26  thf('77', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.05/3.26      inference('sup-', [status(thm)], ['73', '76'])).
% 3.05/3.26  thf('78', plain,
% 3.05/3.26      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['1', '11'])).
% 3.05/3.26  thf('79', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)
% 3.05/3.26        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1))),
% 3.05/3.26      inference('demod', [status(thm)], ['77', '78'])).
% 3.05/3.26  thf('80', plain,
% 3.05/3.26      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_C_1)),
% 3.05/3.26      inference('simplify', [status(thm)], ['79'])).
% 3.05/3.26  thf('81', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.05/3.26         (~ (r2_hidden @ X0 @ X1)
% 3.05/3.26          | (r2_hidden @ X0 @ X2)
% 3.05/3.26          | ~ (r1_tarski @ X1 @ X2))),
% 3.05/3.26      inference('cnf', [status(esa)], [d3_tarski])).
% 3.05/3.26  thf('82', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         ((r2_hidden @ X0 @ sk_C_1)
% 3.05/3.26          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['80', '81'])).
% 3.05/3.26  thf('83', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 3.05/3.26          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 3.05/3.26             sk_C_1))),
% 3.05/3.26      inference('sup-', [status(thm)], ['48', '82'])).
% 3.05/3.26  thf('84', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('85', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.05/3.26         (~ (r2_hidden @ X0 @ X1)
% 3.05/3.26          | (r2_hidden @ X0 @ X2)
% 3.05/3.26          | ~ (r1_tarski @ X1 @ X2))),
% 3.05/3.26      inference('cnf', [status(esa)], [d3_tarski])).
% 3.05/3.26  thf('86', plain,
% 3.05/3.26      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 3.05/3.26      inference('sup-', [status(thm)], ['84', '85'])).
% 3.05/3.26  thf('87', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ X0)
% 3.05/3.26          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)) @ 
% 3.05/3.26             sk_D_1))),
% 3.05/3.26      inference('sup-', [status(thm)], ['83', '86'])).
% 3.05/3.26  thf('88', plain,
% 3.05/3.26      (![X1 : $i, X3 : $i]:
% 3.05/3.26         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.05/3.26      inference('cnf', [status(esa)], [d3_tarski])).
% 3.05/3.26  thf('89', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)
% 3.05/3.26        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1))),
% 3.05/3.26      inference('sup-', [status(thm)], ['87', '88'])).
% 3.05/3.26  thf('90', plain,
% 3.05/3.26      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ sk_D_1)),
% 3.05/3.26      inference('simplify', [status(thm)], ['89'])).
% 3.05/3.26  thf('91', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.05/3.26         (~ (r2_hidden @ X0 @ X1)
% 3.05/3.26          | (r2_hidden @ X0 @ X2)
% 3.05/3.26          | ~ (r1_tarski @ X1 @ X2))),
% 3.05/3.26      inference('cnf', [status(esa)], [d3_tarski])).
% 3.05/3.26  thf('92', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         ((r2_hidden @ X0 @ sk_D_1)
% 3.05/3.26          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['90', '91'])).
% 3.05/3.26  thf('93', plain,
% 3.05/3.26      ((r2_hidden @ 
% 3.05/3.26        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26        sk_D_1)),
% 3.05/3.26      inference('sup-', [status(thm)], ['47', '92'])).
% 3.05/3.26  thf('94', plain,
% 3.05/3.26      ((r2_hidden @ 
% 3.05/3.26        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26        (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 3.05/3.26      inference('clc', [status(thm)], ['45', '46'])).
% 3.05/3.26  thf('95', plain,
% 3.05/3.26      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('96', plain,
% 3.05/3.26      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 3.05/3.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 3.05/3.26          | ~ (r2_hidden @ X10 @ (k3_orders_2 @ X11 @ X12 @ X13))
% 3.05/3.26          | (r2_orders_2 @ X11 @ X10 @ X13)
% 3.05/3.26          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 3.05/3.26          | ~ (l1_orders_2 @ X11)
% 3.05/3.26          | ~ (v5_orders_2 @ X11)
% 3.05/3.26          | ~ (v4_orders_2 @ X11)
% 3.05/3.26          | ~ (v3_orders_2 @ X11)
% 3.05/3.26          | (v2_struct_0 @ X11))),
% 3.05/3.26      inference('cnf', [status(esa)], [t57_orders_2])).
% 3.05/3.26  thf('97', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i]:
% 3.05/3.26         ((v2_struct_0 @ sk_A)
% 3.05/3.26          | ~ (v3_orders_2 @ sk_A)
% 3.05/3.26          | ~ (v4_orders_2 @ sk_A)
% 3.05/3.26          | ~ (v5_orders_2 @ sk_A)
% 3.05/3.26          | ~ (l1_orders_2 @ sk_A)
% 3.05/3.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 3.05/3.26          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 3.05/3.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['95', '96'])).
% 3.05/3.26  thf('98', plain, ((v3_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('99', plain, ((v4_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('100', plain, ((v5_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('101', plain, ((l1_orders_2 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('102', plain,
% 3.05/3.26      (![X0 : $i, X1 : $i]:
% 3.05/3.26         ((v2_struct_0 @ sk_A)
% 3.05/3.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.05/3.26          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 3.05/3.26          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ X0))
% 3.05/3.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 3.05/3.26  thf('103', plain,
% 3.05/3.26      ((~ (m1_subset_1 @ 
% 3.05/3.26           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           (u1_struct_0 @ sk_A))
% 3.05/3.26        | (r2_orders_2 @ sk_A @ 
% 3.05/3.26           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           sk_B)
% 3.05/3.26        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.05/3.26        | (v2_struct_0 @ sk_A))),
% 3.05/3.26      inference('sup-', [status(thm)], ['94', '102'])).
% 3.05/3.26  thf('104', plain,
% 3.05/3.26      ((m1_subset_1 @ 
% 3.05/3.26        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26        (u1_struct_0 @ sk_A))),
% 3.05/3.26      inference('clc', [status(thm)], ['27', '28'])).
% 3.05/3.26  thf('105', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('106', plain,
% 3.05/3.26      (((r2_orders_2 @ sk_A @ 
% 3.05/3.26         (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26          (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26         sk_B)
% 3.05/3.26        | (v2_struct_0 @ sk_A))),
% 3.05/3.26      inference('demod', [status(thm)], ['103', '104', '105'])).
% 3.05/3.26  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('108', plain,
% 3.05/3.26      ((r2_orders_2 @ sk_A @ 
% 3.05/3.26        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26        sk_B)),
% 3.05/3.26      inference('clc', [status(thm)], ['106', '107'])).
% 3.05/3.26  thf('109', plain,
% 3.05/3.26      (((v2_struct_0 @ sk_A)
% 3.05/3.26        | (r2_hidden @ 
% 3.05/3.26           (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26            (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26           (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 3.05/3.26      inference('demod', [status(thm)], ['40', '93', '108'])).
% 3.05/3.26  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 3.05/3.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.26  thf('111', plain,
% 3.05/3.26      ((r2_hidden @ 
% 3.05/3.26        (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.05/3.26      inference('clc', [status(thm)], ['109', '110'])).
% 3.05/3.26  thf('112', plain,
% 3.05/3.26      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ 
% 3.05/3.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['13', '23'])).
% 3.05/3.26  thf('113', plain,
% 3.05/3.26      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.05/3.26          | (r1_tarski @ X6 @ X4)
% 3.05/3.26          | ~ (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X4)
% 3.05/3.26          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.05/3.26      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.05/3.26  thf('114', plain,
% 3.05/3.26      (![X0 : $i]:
% 3.05/3.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.05/3.26          | ~ (r2_hidden @ 
% 3.05/3.26               (sk_D @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B) @ X0 @ 
% 3.05/3.26                (u1_struct_0 @ sk_A)) @ 
% 3.05/3.26               (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.05/3.26          | (r1_tarski @ X0 @ (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['112', '113'])).
% 3.05/3.26  thf('115', plain,
% 3.05/3.26      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26         (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))
% 3.05/3.26        | ~ (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.05/3.26      inference('sup-', [status(thm)], ['111', '114'])).
% 3.05/3.26  thf('116', plain,
% 3.05/3.26      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.05/3.26      inference('sup-', [status(thm)], ['1', '11'])).
% 3.05/3.26  thf('117', plain,
% 3.05/3.26      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_1 @ sk_B) @ 
% 3.05/3.26        (k3_orders_2 @ sk_A @ sk_D_1 @ sk_B))),
% 3.05/3.26      inference('demod', [status(thm)], ['115', '116'])).
% 3.05/3.26  thf('118', plain, ($false), inference('demod', [status(thm)], ['0', '117'])).
% 3.05/3.26  
% 3.05/3.26  % SZS output end Refutation
% 3.05/3.26  
% 3.05/3.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
