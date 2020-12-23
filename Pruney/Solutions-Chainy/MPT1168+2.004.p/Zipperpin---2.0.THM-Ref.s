%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4G8lmGJLh5

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:08 EST 2020

% Result     : Theorem 8.61s
% Output     : Refutation 8.61s
% Verified   : 
% Statistics : Number of formulae       :  223 (1730 expanded)
%              Number of leaves         :   28 ( 509 expanded)
%              Depth                    :   27
%              Number of atoms          : 2843 (42281 expanded)
%              Number of equality atoms :   21 ( 880 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t71_orders_2,conjecture,(
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
                 => ( ( ( r2_hidden @ B @ C )
                      & ( m1_orders_2 @ C @ A @ D ) )
                   => ( ( k3_orders_2 @ A @ C @ B )
                      = ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) )).

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
                   => ( ( ( r2_hidden @ B @ C )
                        & ( m1_orders_2 @ C @ A @ D ) )
                     => ( ( k3_orders_2 @ A @ C @ B )
                        = ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_orders_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ X0 ) @ X0 )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','29'])).

thf('31',plain,
    ( ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B )
 != ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('36',plain,(
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

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ~ ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('47',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ X1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ X1 ) @ sk_C_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B )
 != ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
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
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('78',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_orders_2,axiom,(
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
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( ( r2_orders_2 @ A @ B @ C )
                          & ( r2_hidden @ B @ D )
                          & ( r2_hidden @ C @ E )
                          & ( m1_orders_2 @ E @ A @ D ) )
                       => ( r2_hidden @ B @ E ) ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r2_orders_2 @ X24 @ X23 @ X26 )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( m1_orders_2 @ X27 @ X24 @ X25 )
      | ( r2_hidden @ X23 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_orders_2])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_orders_2 @ X1 @ sk_A @ sk_D )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_orders_2 @ X1 @ sk_A @ sk_D )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( m1_orders_2 @ sk_C_2 @ sk_A @ sk_D )
      | ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,(
    m1_orders_2 @ sk_C_2 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','89'])).

thf('91',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['60','61'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('92',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
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

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('112',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ sk_D )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ sk_D ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D ) ),
    inference('sup-',[status(thm)],['91','115'])).

thf('117',plain,(
    m1_orders_2 @ sk_C_2 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf('119',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ X22 @ X20 )
      | ~ ( m1_orders_2 @ X22 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( r1_tarski @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( r1_tarski @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_D )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    r1_tarski @ sk_C_2 @ sk_D ),
    inference('sup-',[status(thm)],['117','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D ),
    inference(clc,[status(thm)],['116','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['90','131'])).

thf('133',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','132'])).

thf('134',plain,(
    r2_hidden @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_2 ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('141',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('142',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
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

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['144','145','146','147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ X1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B )
 != ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('159',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('161',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    r2_orders_2 @ sk_A @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','139','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('170',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B )
 != ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['170','171'])).

thf('173',plain,(
    r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('174',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_orders_2,axiom,(
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

thf('177',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k3_orders_2 @ X17 @ X19 @ X16 ) @ ( k3_orders_2 @ X17 @ X18 @ X16 ) )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_orders_2])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ X0 @ X1 ) @ ( k3_orders_2 @ sk_A @ sk_D @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ X0 @ X1 ) @ ( k3_orders_2 @ sk_A @ sk_D @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( r1_tarski @ sk_C_2 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','183'])).

thf('185',plain,(
    r1_tarski @ sk_C_2 @ sk_D ),
    inference('sup-',[status(thm)],['117','127'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_2 @ X0 ) @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['174','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    r2_hidden @ ( sk_C_1 @ ( k3_orders_2 @ sk_A @ sk_C_2 @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['173','191'])).

thf('193',plain,(
    $false ),
    inference(demod,[status(thm)],['172','192'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4G8lmGJLh5
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:59:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.61/8.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.61/8.83  % Solved by: fo/fo7.sh
% 8.61/8.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.61/8.83  % done 1999 iterations in 8.341s
% 8.61/8.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.61/8.83  % SZS output start Refutation
% 8.61/8.83  thf(sk_D_type, type, sk_D: $i).
% 8.61/8.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.61/8.83  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 8.61/8.83  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 8.61/8.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.61/8.83  thf(sk_C_2_type, type, sk_C_2: $i).
% 8.61/8.83  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 8.61/8.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.61/8.83  thf(sk_B_type, type, sk_B: $i).
% 8.61/8.83  thf(sk_A_type, type, sk_A: $i).
% 8.61/8.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.61/8.83  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 8.61/8.83  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 8.61/8.83  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 8.61/8.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.61/8.83  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 8.61/8.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.61/8.83  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 8.61/8.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.61/8.83  thf(t2_tarski, axiom,
% 8.61/8.83    (![A:$i,B:$i]:
% 8.61/8.83     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 8.61/8.83       ( ( A ) = ( B ) ) ))).
% 8.61/8.83  thf('0', plain,
% 8.61/8.83      (![X4 : $i, X5 : $i]:
% 8.61/8.83         (((X5) = (X4))
% 8.61/8.83          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 8.61/8.83          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 8.61/8.83      inference('cnf', [status(esa)], [t2_tarski])).
% 8.61/8.83  thf(t71_orders_2, conjecture,
% 8.61/8.83    (![A:$i]:
% 8.61/8.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.61/8.83         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.61/8.83       ( ![B:$i]:
% 8.61/8.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.61/8.83           ( ![C:$i]:
% 8.61/8.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83               ( ![D:$i]:
% 8.61/8.83                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83                   ( ( ( r2_hidden @ B @ C ) & ( m1_orders_2 @ C @ A @ D ) ) =>
% 8.61/8.83                     ( ( k3_orders_2 @ A @ C @ B ) =
% 8.61/8.83                       ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 8.61/8.83  thf(zf_stmt_0, negated_conjecture,
% 8.61/8.83    (~( ![A:$i]:
% 8.61/8.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.61/8.83            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.61/8.83          ( ![B:$i]:
% 8.61/8.83            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.61/8.83              ( ![C:$i]:
% 8.61/8.83                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83                  ( ![D:$i]:
% 8.61/8.83                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83                      ( ( ( r2_hidden @ B @ C ) & ( m1_orders_2 @ C @ A @ D ) ) =>
% 8.61/8.83                        ( ( k3_orders_2 @ A @ C @ B ) =
% 8.61/8.83                          ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 8.61/8.83    inference('cnf.neg', [status(esa)], [t71_orders_2])).
% 8.61/8.83  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('2', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf(dt_k3_orders_2, axiom,
% 8.61/8.83    (![A:$i,B:$i,C:$i]:
% 8.61/8.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.61/8.83         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 8.61/8.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 8.61/8.83         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83       ( m1_subset_1 @
% 8.61/8.83         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.61/8.83  thf('3', plain,
% 8.61/8.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 8.61/8.83          | ~ (l1_orders_2 @ X10)
% 8.61/8.83          | ~ (v5_orders_2 @ X10)
% 8.61/8.83          | ~ (v4_orders_2 @ X10)
% 8.61/8.83          | ~ (v3_orders_2 @ X10)
% 8.61/8.83          | (v2_struct_0 @ X10)
% 8.61/8.83          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 8.61/8.83          | (m1_subset_1 @ (k3_orders_2 @ X10 @ X9 @ X11) @ 
% 8.61/8.83             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 8.61/8.83      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 8.61/8.83  thf('4', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ 
% 8.61/8.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['2', '3'])).
% 8.61/8.83  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('6', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('9', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ 
% 8.61/8.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 8.61/8.83  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('11', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ 
% 8.61/8.83             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.61/8.83      inference('clc', [status(thm)], ['9', '10'])).
% 8.61/8.83  thf('12', plain,
% 8.61/8.83      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['1', '11'])).
% 8.61/8.83  thf(t4_subset, axiom,
% 8.61/8.83    (![A:$i,B:$i,C:$i]:
% 8.61/8.83     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 8.61/8.83       ( m1_subset_1 @ A @ C ) ))).
% 8.61/8.83  thf('13', plain,
% 8.61/8.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.61/8.83         (~ (r2_hidden @ X6 @ X7)
% 8.61/8.83          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 8.61/8.83          | (m1_subset_1 @ X6 @ X8))),
% 8.61/8.83      inference('cnf', [status(esa)], [t4_subset])).
% 8.61/8.83  thf('14', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['12', '13'])).
% 8.61/8.83  thf('15', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r2_hidden @ (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ X0) @ 
% 8.61/8.83           X0)
% 8.61/8.83          | ((X0) = (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83          | (m1_subset_1 @ 
% 8.61/8.83             (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ X0) @ 
% 8.61/8.83             (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['0', '14'])).
% 8.61/8.83  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('17', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('18', plain,
% 8.61/8.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 8.61/8.83          | ~ (l1_orders_2 @ X10)
% 8.61/8.83          | ~ (v5_orders_2 @ X10)
% 8.61/8.83          | ~ (v4_orders_2 @ X10)
% 8.61/8.83          | ~ (v3_orders_2 @ X10)
% 8.61/8.83          | (v2_struct_0 @ X10)
% 8.61/8.83          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 8.61/8.83          | (m1_subset_1 @ (k3_orders_2 @ X10 @ X9 @ X11) @ 
% 8.61/8.83             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 8.61/8.83      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 8.61/8.83  thf('19', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 8.61/8.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['17', '18'])).
% 8.61/8.83  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('24', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 8.61/8.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 8.61/8.83  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('26', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 8.61/8.83             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.61/8.83      inference('clc', [status(thm)], ['24', '25'])).
% 8.61/8.83  thf('27', plain,
% 8.61/8.83      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 8.61/8.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['16', '26'])).
% 8.61/8.83  thf('28', plain,
% 8.61/8.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.61/8.83         (~ (r2_hidden @ X6 @ X7)
% 8.61/8.83          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 8.61/8.83          | (m1_subset_1 @ X6 @ X8))),
% 8.61/8.83      inference('cnf', [status(esa)], [t4_subset])).
% 8.61/8.83  thf('29', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['27', '28'])).
% 8.61/8.83  thf('30', plain,
% 8.61/8.83      (((m1_subset_1 @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         (u1_struct_0 @ sk_A))
% 8.61/8.83        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B)
% 8.61/8.83            = (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83        | (m1_subset_1 @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['15', '29'])).
% 8.61/8.83  thf('31', plain,
% 8.61/8.83      ((((k3_orders_2 @ sk_A @ sk_D @ sk_B)
% 8.61/8.83          = (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83        | (m1_subset_1 @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('simplify', [status(thm)], ['30'])).
% 8.61/8.83  thf('32', plain,
% 8.61/8.83      (((k3_orders_2 @ sk_A @ sk_C_2 @ sk_B)
% 8.61/8.83         != (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('33', plain,
% 8.61/8.83      ((m1_subset_1 @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 8.61/8.83  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('35', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf(t57_orders_2, axiom,
% 8.61/8.83    (![A:$i]:
% 8.61/8.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.61/8.83         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.61/8.83       ( ![B:$i]:
% 8.61/8.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.61/8.83           ( ![C:$i]:
% 8.61/8.83             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 8.61/8.83               ( ![D:$i]:
% 8.61/8.83                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 8.61/8.83                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 8.61/8.83  thf('36', plain,
% 8.61/8.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 8.61/8.83          | ~ (r2_orders_2 @ X13 @ X12 @ X15)
% 8.61/8.83          | ~ (r2_hidden @ X12 @ X14)
% 8.61/8.83          | (r2_hidden @ X12 @ (k3_orders_2 @ X13 @ X14 @ X15))
% 8.61/8.83          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (l1_orders_2 @ X13)
% 8.61/8.83          | ~ (v5_orders_2 @ X13)
% 8.61/8.83          | ~ (v4_orders_2 @ X13)
% 8.61/8.83          | ~ (v3_orders_2 @ X13)
% 8.61/8.83          | (v2_struct_0 @ X13))),
% 8.61/8.83      inference('cnf', [status(esa)], [t57_orders_2])).
% 8.61/8.83  thf('37', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0))
% 8.61/8.83          | ~ (r2_hidden @ X1 @ sk_C_2)
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['35', '36'])).
% 8.61/8.83  thf('38', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('39', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('42', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0))
% 8.61/8.83          | ~ (r2_hidden @ X1 @ sk_C_2)
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 8.61/8.83  thf('43', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B)
% 8.61/8.83          | ~ (r2_hidden @ X0 @ sk_C_2)
% 8.61/8.83          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['34', '42'])).
% 8.61/8.83  thf('44', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83        | ~ (r2_hidden @ 
% 8.61/8.83             (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83              (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             sk_C_2)
% 8.61/8.83        | ~ (r2_orders_2 @ sk_A @ 
% 8.61/8.83             (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83              (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             sk_B))),
% 8.61/8.83      inference('sup-', [status(thm)], ['33', '43'])).
% 8.61/8.83  thf('45', plain,
% 8.61/8.83      ((m1_subset_1 @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 8.61/8.83  thf('46', plain,
% 8.61/8.83      (![X4 : $i, X5 : $i]:
% 8.61/8.83         (((X5) = (X4))
% 8.61/8.83          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 8.61/8.83          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 8.61/8.83      inference('cnf', [status(esa)], [t2_tarski])).
% 8.61/8.83  thf('47', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('48', plain,
% 8.61/8.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 8.61/8.83          | ~ (r2_hidden @ X12 @ (k3_orders_2 @ X13 @ X14 @ X15))
% 8.61/8.83          | (r2_hidden @ X12 @ X14)
% 8.61/8.83          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (l1_orders_2 @ X13)
% 8.61/8.83          | ~ (v5_orders_2 @ X13)
% 8.61/8.83          | ~ (v4_orders_2 @ X13)
% 8.61/8.83          | ~ (v3_orders_2 @ X13)
% 8.61/8.83          | (v2_struct_0 @ X13))),
% 8.61/8.83      inference('cnf', [status(esa)], [t57_orders_2])).
% 8.61/8.83  thf('49', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ X1 @ sk_C_2)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['47', '48'])).
% 8.61/8.83  thf('50', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('51', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('52', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('54', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ X1 @ sk_C_2)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 8.61/8.83  thf('55', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((r2_hidden @ (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ X1) @ X1)
% 8.61/8.83          | ((X1) = (k3_orders_2 @ sk_A @ sk_C_2 @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ 
% 8.61/8.83               (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ X1) @ 
% 8.61/8.83               (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ X1) @ 
% 8.61/8.83             sk_C_2)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['46', '54'])).
% 8.61/8.83  thf('56', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2)
% 8.61/8.83        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B)
% 8.61/8.83            = (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['45', '55'])).
% 8.61/8.83  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('58', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2)
% 8.61/8.83        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B)
% 8.61/8.83            = (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('demod', [status(thm)], ['56', '57'])).
% 8.61/8.83  thf('59', plain,
% 8.61/8.83      (((k3_orders_2 @ sk_A @ sk_C_2 @ sk_B)
% 8.61/8.83         != (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('60', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 8.61/8.83  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('62', plain,
% 8.61/8.83      (((r2_hidden @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2))),
% 8.61/8.83      inference('clc', [status(thm)], ['60', '61'])).
% 8.61/8.83  thf('63', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('64', plain,
% 8.61/8.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 8.61/8.83          | ~ (r2_hidden @ X12 @ (k3_orders_2 @ X13 @ X14 @ X15))
% 8.61/8.83          | (r2_orders_2 @ X13 @ X12 @ X15)
% 8.61/8.83          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (l1_orders_2 @ X13)
% 8.61/8.83          | ~ (v5_orders_2 @ X13)
% 8.61/8.83          | ~ (v4_orders_2 @ X13)
% 8.61/8.83          | ~ (v3_orders_2 @ X13)
% 8.61/8.83          | (v2_struct_0 @ X13))),
% 8.61/8.83      inference('cnf', [status(esa)], [t57_orders_2])).
% 8.61/8.83  thf('65', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['63', '64'])).
% 8.61/8.83  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('67', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('70', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 8.61/8.83  thf('71', plain,
% 8.61/8.83      (((r2_hidden @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         sk_C_2)
% 8.61/8.83        | ~ (m1_subset_1 @ 
% 8.61/8.83             (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83              (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             (u1_struct_0 @ sk_A))
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B)
% 8.61/8.83        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 8.61/8.83        | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['62', '70'])).
% 8.61/8.83  thf('72', plain,
% 8.61/8.83      ((m1_subset_1 @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 8.61/8.83  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('74', plain,
% 8.61/8.83      (((r2_hidden @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         sk_C_2)
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B)
% 8.61/8.83        | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('demod', [status(thm)], ['71', '72', '73'])).
% 8.61/8.83  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('76', plain,
% 8.61/8.83      (((r2_orders_2 @ sk_A @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         sk_B)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2))),
% 8.61/8.83      inference('clc', [status(thm)], ['74', '75'])).
% 8.61/8.83  thf('77', plain,
% 8.61/8.83      ((m1_subset_1 @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 8.61/8.83  thf('78', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('79', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf(t70_orders_2, axiom,
% 8.61/8.83    (![A:$i]:
% 8.61/8.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.61/8.83         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.61/8.83       ( ![B:$i]:
% 8.61/8.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.61/8.83           ( ![C:$i]:
% 8.61/8.83             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 8.61/8.83               ( ![D:$i]:
% 8.61/8.83                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83                   ( ![E:$i]:
% 8.61/8.83                     ( ( m1_subset_1 @
% 8.61/8.83                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83                       ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 8.61/8.83                           ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ E ) & 
% 8.61/8.83                           ( m1_orders_2 @ E @ A @ D ) ) =>
% 8.61/8.83                         ( r2_hidden @ B @ E ) ) ) ) ) ) ) ) ) ) ))).
% 8.61/8.83  thf('80', plain,
% 8.61/8.83      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 8.61/8.83          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.61/8.83          | ~ (r2_orders_2 @ X24 @ X23 @ X26)
% 8.61/8.83          | ~ (r2_hidden @ X23 @ X25)
% 8.61/8.83          | ~ (r2_hidden @ X26 @ X27)
% 8.61/8.83          | ~ (m1_orders_2 @ X27 @ X24 @ X25)
% 8.61/8.83          | (r2_hidden @ X23 @ X27)
% 8.61/8.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.61/8.83          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 8.61/8.83          | ~ (l1_orders_2 @ X24)
% 8.61/8.83          | ~ (v5_orders_2 @ X24)
% 8.61/8.83          | ~ (v4_orders_2 @ X24)
% 8.61/8.83          | ~ (v3_orders_2 @ X24)
% 8.61/8.83          | (v2_struct_0 @ X24))),
% 8.61/8.83      inference('cnf', [status(esa)], [t70_orders_2])).
% 8.61/8.83  thf('81', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.61/8.83          | (r2_hidden @ X2 @ X1)
% 8.61/8.83          | ~ (m1_orders_2 @ X1 @ sk_A @ sk_D)
% 8.61/8.83          | ~ (r2_hidden @ X0 @ X1)
% 8.61/8.83          | ~ (r2_hidden @ X2 @ sk_D)
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ X2 @ X0)
% 8.61/8.83          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['79', '80'])).
% 8.61/8.83  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('86', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.61/8.83          | (r2_hidden @ X2 @ X1)
% 8.61/8.83          | ~ (m1_orders_2 @ X1 @ sk_A @ sk_D)
% 8.61/8.83          | ~ (r2_hidden @ X0 @ X1)
% 8.61/8.83          | ~ (r2_hidden @ X2 @ sk_D)
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ X2 @ X0)
% 8.61/8.83          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 8.61/8.83  thf('87', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 8.61/8.83          | ~ (r2_hidden @ X0 @ sk_D)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ sk_C_2)
% 8.61/8.83          | ~ (m1_orders_2 @ sk_C_2 @ sk_A @ sk_D)
% 8.61/8.83          | (r2_hidden @ X0 @ sk_C_2)
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['78', '86'])).
% 8.61/8.83  thf('88', plain, ((m1_orders_2 @ sk_C_2 @ sk_A @ sk_D)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('89', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 8.61/8.83          | ~ (r2_hidden @ X0 @ sk_D)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ sk_C_2)
% 8.61/8.83          | (r2_hidden @ X0 @ sk_C_2)
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('demod', [status(thm)], ['87', '88'])).
% 8.61/8.83  thf('90', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ 
% 8.61/8.83             (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83              (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             sk_C_2)
% 8.61/8.83          | ~ (r2_hidden @ X0 @ sk_C_2)
% 8.61/8.83          | ~ (r2_hidden @ 
% 8.61/8.83               (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83                (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83               sk_D)
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ 
% 8.61/8.83               (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83                (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83               X0))),
% 8.61/8.83      inference('sup-', [status(thm)], ['77', '89'])).
% 8.61/8.83  thf('91', plain,
% 8.61/8.83      (((r2_hidden @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2))),
% 8.61/8.83      inference('clc', [status(thm)], ['60', '61'])).
% 8.61/8.83  thf(d3_tarski, axiom,
% 8.61/8.83    (![A:$i,B:$i]:
% 8.61/8.83     ( ( r1_tarski @ A @ B ) <=>
% 8.61/8.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.61/8.83  thf('92', plain,
% 8.61/8.83      (![X1 : $i, X3 : $i]:
% 8.61/8.83         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.61/8.83      inference('cnf', [status(esa)], [d3_tarski])).
% 8.61/8.83  thf('93', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['27', '28'])).
% 8.61/8.83  thf('94', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 8.61/8.83          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['92', '93'])).
% 8.61/8.83  thf('95', plain,
% 8.61/8.83      (![X1 : $i, X3 : $i]:
% 8.61/8.83         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.61/8.83      inference('cnf', [status(esa)], [d3_tarski])).
% 8.61/8.83  thf('96', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('97', plain,
% 8.61/8.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 8.61/8.83          | ~ (r2_hidden @ X12 @ (k3_orders_2 @ X13 @ X14 @ X15))
% 8.61/8.83          | (r2_hidden @ X12 @ X14)
% 8.61/8.83          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (l1_orders_2 @ X13)
% 8.61/8.83          | ~ (v5_orders_2 @ X13)
% 8.61/8.83          | ~ (v4_orders_2 @ X13)
% 8.61/8.83          | ~ (v3_orders_2 @ X13)
% 8.61/8.83          | (v2_struct_0 @ X13))),
% 8.61/8.83      inference('cnf', [status(esa)], [t57_orders_2])).
% 8.61/8.83  thf('98', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ X1 @ sk_D)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['96', '97'])).
% 8.61/8.83  thf('99', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('100', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('101', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('102', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('103', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ X1 @ sk_D)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 8.61/8.83  thf('104', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ X1)
% 8.61/8.83          | ~ (m1_subset_1 @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 8.61/8.83               (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ sk_D)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['95', '103'])).
% 8.61/8.83  thf('105', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 8.61/8.83          | (v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             sk_D)
% 8.61/8.83          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 8.61/8.83      inference('sup-', [status(thm)], ['94', '104'])).
% 8.61/8.83  thf('106', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('107', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 8.61/8.83          | (v2_struct_0 @ sk_A)
% 8.61/8.83          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             sk_D)
% 8.61/8.83          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 8.61/8.83      inference('demod', [status(thm)], ['105', '106'])).
% 8.61/8.83  thf('108', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_D)
% 8.61/8.83          | (v2_struct_0 @ sk_A)
% 8.61/8.83          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 8.61/8.83      inference('simplify', [status(thm)], ['107'])).
% 8.61/8.83  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('110', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 8.61/8.83          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             sk_D))),
% 8.61/8.83      inference('clc', [status(thm)], ['108', '109'])).
% 8.61/8.83  thf('111', plain,
% 8.61/8.83      (![X1 : $i, X3 : $i]:
% 8.61/8.83         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 8.61/8.83      inference('cnf', [status(esa)], [d3_tarski])).
% 8.61/8.83  thf('112', plain,
% 8.61/8.83      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ sk_D)
% 8.61/8.83        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ sk_D))),
% 8.61/8.83      inference('sup-', [status(thm)], ['110', '111'])).
% 8.61/8.83  thf('113', plain, ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ sk_D)),
% 8.61/8.83      inference('simplify', [status(thm)], ['112'])).
% 8.61/8.83  thf('114', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.61/8.83         (~ (r2_hidden @ X0 @ X1)
% 8.61/8.83          | (r2_hidden @ X0 @ X2)
% 8.61/8.83          | ~ (r1_tarski @ X1 @ X2))),
% 8.61/8.83      inference('cnf', [status(esa)], [d3_tarski])).
% 8.61/8.83  thf('115', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r2_hidden @ X0 @ sk_D)
% 8.61/8.83          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['113', '114'])).
% 8.61/8.83  thf('116', plain,
% 8.61/8.83      (((r2_hidden @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         sk_C_2)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_D))),
% 8.61/8.83      inference('sup-', [status(thm)], ['91', '115'])).
% 8.61/8.83  thf('117', plain, ((m1_orders_2 @ sk_C_2 @ sk_A @ sk_D)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('118', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf(t67_orders_2, axiom,
% 8.61/8.83    (![A:$i]:
% 8.61/8.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.61/8.83         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.61/8.83       ( ![B:$i]:
% 8.61/8.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 8.61/8.83  thf('119', plain,
% 8.61/8.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 8.61/8.83          | (r1_tarski @ X22 @ X20)
% 8.61/8.83          | ~ (m1_orders_2 @ X22 @ X21 @ X20)
% 8.61/8.83          | ~ (l1_orders_2 @ X21)
% 8.61/8.83          | ~ (v5_orders_2 @ X21)
% 8.61/8.83          | ~ (v4_orders_2 @ X21)
% 8.61/8.83          | ~ (v3_orders_2 @ X21)
% 8.61/8.83          | (v2_struct_0 @ X21))),
% 8.61/8.83      inference('cnf', [status(esa)], [t67_orders_2])).
% 8.61/8.83  thf('120', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A)
% 8.61/8.83          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 8.61/8.83          | (r1_tarski @ X0 @ sk_D))),
% 8.61/8.83      inference('sup-', [status(thm)], ['118', '119'])).
% 8.61/8.83  thf('121', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('122', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('123', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('124', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('125', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 8.61/8.83          | (r1_tarski @ X0 @ sk_D))),
% 8.61/8.83      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 8.61/8.83  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('127', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 8.61/8.83      inference('clc', [status(thm)], ['125', '126'])).
% 8.61/8.83  thf('128', plain, ((r1_tarski @ sk_C_2 @ sk_D)),
% 8.61/8.83      inference('sup-', [status(thm)], ['117', '127'])).
% 8.61/8.83  thf('129', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.61/8.83         (~ (r2_hidden @ X0 @ X1)
% 8.61/8.83          | (r2_hidden @ X0 @ X2)
% 8.61/8.83          | ~ (r1_tarski @ X1 @ X2))),
% 8.61/8.83      inference('cnf', [status(esa)], [d3_tarski])).
% 8.61/8.83  thf('130', plain,
% 8.61/8.83      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 8.61/8.83      inference('sup-', [status(thm)], ['128', '129'])).
% 8.61/8.83  thf('131', plain,
% 8.61/8.83      ((r2_hidden @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        sk_D)),
% 8.61/8.83      inference('clc', [status(thm)], ['116', '130'])).
% 8.61/8.83  thf('132', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_hidden @ 
% 8.61/8.83             (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83              (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             sk_C_2)
% 8.61/8.83          | ~ (r2_hidden @ X0 @ sk_C_2)
% 8.61/8.83          | ~ (r2_orders_2 @ sk_A @ 
% 8.61/8.83               (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83                (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83               X0))),
% 8.61/8.83      inference('demod', [status(thm)], ['90', '131'])).
% 8.61/8.83  thf('133', plain,
% 8.61/8.83      (((r2_hidden @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         sk_C_2)
% 8.61/8.83        | ~ (r2_hidden @ sk_B @ sk_C_2)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2)
% 8.61/8.83        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 8.61/8.83        | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['76', '132'])).
% 8.61/8.83  thf('134', plain, ((r2_hidden @ sk_B @ sk_C_2)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('135', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('136', plain,
% 8.61/8.83      (((r2_hidden @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         sk_C_2)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2)
% 8.61/8.83        | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('demod', [status(thm)], ['133', '134', '135'])).
% 8.61/8.83  thf('137', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_C_2))),
% 8.61/8.83      inference('simplify', [status(thm)], ['136'])).
% 8.61/8.83  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('139', plain,
% 8.61/8.83      ((r2_hidden @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        sk_C_2)),
% 8.61/8.83      inference('clc', [status(thm)], ['137', '138'])).
% 8.61/8.83  thf('140', plain,
% 8.61/8.83      ((m1_subset_1 @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 8.61/8.83  thf('141', plain,
% 8.61/8.83      (![X4 : $i, X5 : $i]:
% 8.61/8.83         (((X5) = (X4))
% 8.61/8.83          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 8.61/8.83          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 8.61/8.83      inference('cnf', [status(esa)], [t2_tarski])).
% 8.61/8.83  thf('142', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('143', plain,
% 8.61/8.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 8.61/8.83          | ~ (r2_hidden @ X12 @ (k3_orders_2 @ X13 @ X14 @ X15))
% 8.61/8.83          | (r2_orders_2 @ X13 @ X12 @ X15)
% 8.61/8.83          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 8.61/8.83          | ~ (l1_orders_2 @ X13)
% 8.61/8.83          | ~ (v5_orders_2 @ X13)
% 8.61/8.83          | ~ (v4_orders_2 @ X13)
% 8.61/8.83          | ~ (v3_orders_2 @ X13)
% 8.61/8.83          | (v2_struct_0 @ X13))),
% 8.61/8.83      inference('cnf', [status(esa)], [t57_orders_2])).
% 8.61/8.83  thf('144', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['142', '143'])).
% 8.61/8.83  thf('145', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('146', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('147', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('148', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('149', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('demod', [status(thm)], ['144', '145', '146', '147', '148'])).
% 8.61/8.83  thf('150', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((r2_hidden @ (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ X1) @ X1)
% 8.61/8.83          | ((X1) = (k3_orders_2 @ sk_A @ sk_C_2 @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ 
% 8.61/8.83               (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ X1) @ 
% 8.61/8.83               (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_orders_2 @ sk_A @ 
% 8.61/8.83             (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ X1) @ X0)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['141', '149'])).
% 8.61/8.83  thf('151', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B)
% 8.61/8.83        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B)
% 8.61/8.83            = (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['140', '150'])).
% 8.61/8.83  thf('152', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('153', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B)
% 8.61/8.83        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B)
% 8.61/8.83            = (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('demod', [status(thm)], ['151', '152'])).
% 8.61/8.83  thf('154', plain,
% 8.61/8.83      (((k3_orders_2 @ sk_A @ sk_C_2 @ sk_B)
% 8.61/8.83         != (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('155', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['153', '154'])).
% 8.61/8.83  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('157', plain,
% 8.61/8.83      (((r2_hidden @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B))),
% 8.61/8.83      inference('clc', [status(thm)], ['155', '156'])).
% 8.61/8.83  thf('158', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 8.61/8.83          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 8.61/8.83  thf('159', plain,
% 8.61/8.83      (((r2_orders_2 @ sk_A @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         sk_B)
% 8.61/8.83        | ~ (m1_subset_1 @ 
% 8.61/8.83             (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83              (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83             (u1_struct_0 @ sk_A))
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B)
% 8.61/8.83        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 8.61/8.83        | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['157', '158'])).
% 8.61/8.83  thf('160', plain,
% 8.61/8.83      ((m1_subset_1 @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 8.61/8.83  thf('161', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('162', plain,
% 8.61/8.83      (((r2_orders_2 @ sk_A @ 
% 8.61/8.83         (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83         sk_B)
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B)
% 8.61/8.83        | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('demod', [status(thm)], ['159', '160', '161'])).
% 8.61/8.83  thf('163', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | (r2_orders_2 @ sk_A @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           sk_B))),
% 8.61/8.83      inference('simplify', [status(thm)], ['162'])).
% 8.61/8.83  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('165', plain,
% 8.61/8.83      ((r2_orders_2 @ sk_A @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        sk_B)),
% 8.61/8.83      inference('clc', [status(thm)], ['163', '164'])).
% 8.61/8.83  thf('166', plain,
% 8.61/8.83      (((v2_struct_0 @ sk_A)
% 8.61/8.83        | (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B)))),
% 8.61/8.83      inference('demod', [status(thm)], ['44', '139', '165'])).
% 8.61/8.83  thf('167', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('168', plain,
% 8.61/8.83      ((r2_hidden @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))),
% 8.61/8.83      inference('clc', [status(thm)], ['166', '167'])).
% 8.61/8.83  thf('169', plain,
% 8.61/8.83      (![X4 : $i, X5 : $i]:
% 8.61/8.83         (((X5) = (X4))
% 8.61/8.83          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 8.61/8.83          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 8.61/8.83      inference('cnf', [status(esa)], [t2_tarski])).
% 8.61/8.83  thf('170', plain,
% 8.61/8.83      ((~ (r2_hidden @ 
% 8.61/8.83           (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83            (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 8.61/8.83        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B)
% 8.61/8.83            = (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['168', '169'])).
% 8.61/8.83  thf('171', plain,
% 8.61/8.83      (((k3_orders_2 @ sk_A @ sk_C_2 @ sk_B)
% 8.61/8.83         != (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('172', plain,
% 8.61/8.83      (~ (r2_hidden @ 
% 8.61/8.83          (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83          (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 8.61/8.83      inference('simplify_reflect-', [status(thm)], ['170', '171'])).
% 8.61/8.83  thf('173', plain,
% 8.61/8.83      ((r2_hidden @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B))),
% 8.61/8.83      inference('clc', [status(thm)], ['166', '167'])).
% 8.61/8.83  thf('174', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('175', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('176', plain,
% 8.61/8.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf(t65_orders_2, axiom,
% 8.61/8.83    (![A:$i]:
% 8.61/8.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.61/8.83         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.61/8.83       ( ![B:$i]:
% 8.61/8.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.61/8.83           ( ![C:$i]:
% 8.61/8.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83               ( ![D:$i]:
% 8.61/8.83                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.61/8.83                   ( ( r1_tarski @ C @ D ) =>
% 8.61/8.83                     ( r1_tarski @
% 8.61/8.83                       ( k3_orders_2 @ A @ C @ B ) @ 
% 8.61/8.83                       ( k3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 8.61/8.83  thf('177', plain,
% 8.61/8.83      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 8.61/8.83          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 8.61/8.83          | (r1_tarski @ (k3_orders_2 @ X17 @ X19 @ X16) @ 
% 8.61/8.83             (k3_orders_2 @ X17 @ X18 @ X16))
% 8.61/8.83          | ~ (r1_tarski @ X19 @ X18)
% 8.61/8.83          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 8.61/8.83          | ~ (l1_orders_2 @ X17)
% 8.61/8.83          | ~ (v5_orders_2 @ X17)
% 8.61/8.83          | ~ (v4_orders_2 @ X17)
% 8.61/8.83          | ~ (v3_orders_2 @ X17)
% 8.61/8.83          | (v2_struct_0 @ X17))),
% 8.61/8.83      inference('cnf', [status(esa)], [t65_orders_2])).
% 8.61/8.83  thf('178', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (v3_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v4_orders_2 @ sk_A)
% 8.61/8.83          | ~ (v5_orders_2 @ sk_A)
% 8.61/8.83          | ~ (l1_orders_2 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.61/8.83          | ~ (r1_tarski @ X0 @ sk_D)
% 8.61/8.83          | (r1_tarski @ (k3_orders_2 @ sk_A @ X0 @ X1) @ 
% 8.61/8.83             (k3_orders_2 @ sk_A @ sk_D @ X1))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['176', '177'])).
% 8.61/8.83  thf('179', plain, ((v3_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('180', plain, ((v4_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('181', plain, ((v5_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('182', plain, ((l1_orders_2 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('183', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i]:
% 8.61/8.83         ((v2_struct_0 @ sk_A)
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.61/8.83          | ~ (r1_tarski @ X0 @ sk_D)
% 8.61/8.83          | (r1_tarski @ (k3_orders_2 @ sk_A @ X0 @ X1) @ 
% 8.61/8.83             (k3_orders_2 @ sk_A @ sk_D @ X1))
% 8.61/8.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 8.61/8.83  thf('184', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ 
% 8.61/8.83             (k3_orders_2 @ sk_A @ sk_D @ X0))
% 8.61/8.83          | ~ (r1_tarski @ sk_C_2 @ sk_D)
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('sup-', [status(thm)], ['175', '183'])).
% 8.61/8.83  thf('185', plain, ((r1_tarski @ sk_C_2 @ sk_D)),
% 8.61/8.83      inference('sup-', [status(thm)], ['117', '127'])).
% 8.61/8.83  thf('186', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 8.61/8.83          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ 
% 8.61/8.83             (k3_orders_2 @ sk_A @ sk_D @ X0))
% 8.61/8.83          | (v2_struct_0 @ sk_A))),
% 8.61/8.83      inference('demod', [status(thm)], ['184', '185'])).
% 8.61/8.83  thf('187', plain, (~ (v2_struct_0 @ sk_A)),
% 8.61/8.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.61/8.83  thf('188', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_2 @ X0) @ 
% 8.61/8.83           (k3_orders_2 @ sk_A @ sk_D @ X0))
% 8.61/8.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 8.61/8.83      inference('clc', [status(thm)], ['186', '187'])).
% 8.61/8.83  thf('189', plain,
% 8.61/8.83      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 8.61/8.83      inference('sup-', [status(thm)], ['174', '188'])).
% 8.61/8.83  thf('190', plain,
% 8.61/8.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.61/8.83         (~ (r2_hidden @ X0 @ X1)
% 8.61/8.83          | (r2_hidden @ X0 @ X2)
% 8.61/8.83          | ~ (r1_tarski @ X1 @ X2))),
% 8.61/8.83      inference('cnf', [status(esa)], [d3_tarski])).
% 8.61/8.83  thf('191', plain,
% 8.61/8.83      (![X0 : $i]:
% 8.61/8.83         ((r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B))
% 8.61/8.83          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B)))),
% 8.61/8.83      inference('sup-', [status(thm)], ['189', '190'])).
% 8.61/8.83  thf('192', plain,
% 8.61/8.83      ((r2_hidden @ 
% 8.61/8.83        (sk_C_1 @ (k3_orders_2 @ sk_A @ sk_C_2 @ sk_B) @ 
% 8.61/8.83         (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 8.61/8.83        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 8.61/8.83      inference('sup-', [status(thm)], ['173', '191'])).
% 8.61/8.83  thf('193', plain, ($false), inference('demod', [status(thm)], ['172', '192'])).
% 8.61/8.83  
% 8.61/8.83  % SZS output end Refutation
% 8.61/8.83  
% 8.61/8.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
