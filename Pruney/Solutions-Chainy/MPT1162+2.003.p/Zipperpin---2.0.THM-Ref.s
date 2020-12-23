%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kh98VgDQxP

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:03 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 280 expanded)
%              Number of leaves         :   23 (  92 expanded)
%              Depth                    :   25
%              Number of atoms          : 1381 (5968 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ~ ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('4',plain,(
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

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k3_orders_2 @ X15 @ X16 @ X17 ) )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('20',plain,(
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
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k3_orders_2 @ X15 @ X16 @ X17 ) )
      | ( r2_orders_2 @ X15 @ X14 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

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

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( r2_orders_2 @ X11 @ X10 @ X12 )
      | ~ ( r2_orders_2 @ X11 @ X13 @ X12 )
      | ~ ( r2_orders_2 @ X11 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_orders_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X2 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X2 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','61'])).

thf('63',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_orders_2 @ X15 @ X14 @ X17 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ( r2_hidden @ X14 @ ( k3_orders_2 @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['0','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kh98VgDQxP
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.24/2.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.24/2.47  % Solved by: fo/fo7.sh
% 2.24/2.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.24/2.47  % done 1176 iterations in 2.019s
% 2.24/2.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.24/2.47  % SZS output start Refutation
% 2.24/2.47  thf(sk_A_type, type, sk_A: $i).
% 2.24/2.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.24/2.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.24/2.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.24/2.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.24/2.47  thf(sk_D_type, type, sk_D: $i).
% 2.24/2.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.24/2.47  thf(sk_B_type, type, sk_B: $i).
% 2.24/2.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 2.24/2.47  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 2.24/2.47  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 2.24/2.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.24/2.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.24/2.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 2.24/2.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 2.24/2.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 2.24/2.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.24/2.47  thf(t64_orders_2, conjecture,
% 2.24/2.47    (![A:$i]:
% 2.24/2.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.24/2.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.24/2.47       ( ![B:$i]:
% 2.24/2.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47           ( ![C:$i]:
% 2.24/2.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47               ( ![D:$i]:
% 2.24/2.47                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47                   ( ( r2_orders_2 @ A @ B @ C ) =>
% 2.24/2.47                     ( r1_tarski @
% 2.24/2.47                       ( k3_orders_2 @ A @ D @ B ) @ 
% 2.24/2.47                       ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 2.24/2.47  thf(zf_stmt_0, negated_conjecture,
% 2.24/2.47    (~( ![A:$i]:
% 2.24/2.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.24/2.47            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.24/2.47          ( ![B:$i]:
% 2.24/2.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47              ( ![C:$i]:
% 2.24/2.47                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47                  ( ![D:$i]:
% 2.24/2.47                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47                      ( ( r2_orders_2 @ A @ B @ C ) =>
% 2.24/2.47                        ( r1_tarski @
% 2.24/2.47                          ( k3_orders_2 @ A @ D @ B ) @ 
% 2.24/2.47                          ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 2.24/2.47    inference('cnf.neg', [status(esa)], [t64_orders_2])).
% 2.24/2.47  thf('0', plain,
% 2.24/2.47      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 2.24/2.47          (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf(d3_tarski, axiom,
% 2.24/2.47    (![A:$i,B:$i]:
% 2.24/2.47     ( ( r1_tarski @ A @ B ) <=>
% 2.24/2.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.24/2.47  thf('1', plain,
% 2.24/2.47      (![X1 : $i, X3 : $i]:
% 2.24/2.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.24/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.24/2.47  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('3', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf(dt_k3_orders_2, axiom,
% 2.24/2.47    (![A:$i,B:$i,C:$i]:
% 2.24/2.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.24/2.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 2.24/2.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 2.24/2.47         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47       ( m1_subset_1 @
% 2.24/2.47         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.24/2.47  thf('4', plain,
% 2.24/2.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 2.24/2.47          | ~ (l1_orders_2 @ X8)
% 2.24/2.47          | ~ (v5_orders_2 @ X8)
% 2.24/2.47          | ~ (v4_orders_2 @ X8)
% 2.24/2.47          | ~ (v3_orders_2 @ X8)
% 2.24/2.47          | (v2_struct_0 @ X8)
% 2.24/2.47          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 2.24/2.47          | (m1_subset_1 @ (k3_orders_2 @ X8 @ X7 @ X9) @ 
% 2.24/2.47             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 2.24/2.47      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 2.24/2.47  thf('5', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 2.24/2.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (v3_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v4_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v5_orders_2 @ sk_A)
% 2.24/2.47          | ~ (l1_orders_2 @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['3', '4'])).
% 2.24/2.47  thf('6', plain, ((v3_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('7', plain, ((v4_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('8', plain, ((v5_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('10', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 2.24/2.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (v2_struct_0 @ sk_A))),
% 2.24/2.47      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 2.24/2.47  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('12', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 2.24/2.47             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.24/2.47      inference('clc', [status(thm)], ['10', '11'])).
% 2.24/2.47  thf('13', plain,
% 2.24/2.47      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 2.24/2.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['2', '12'])).
% 2.24/2.47  thf(t4_subset, axiom,
% 2.24/2.47    (![A:$i,B:$i,C:$i]:
% 2.24/2.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.24/2.47       ( m1_subset_1 @ A @ C ) ))).
% 2.24/2.47  thf('14', plain,
% 2.24/2.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.24/2.47         (~ (r2_hidden @ X4 @ X5)
% 2.24/2.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 2.24/2.47          | (m1_subset_1 @ X4 @ X6))),
% 2.24/2.47      inference('cnf', [status(esa)], [t4_subset])).
% 2.24/2.47  thf('15', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['13', '14'])).
% 2.24/2.47  thf('16', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['1', '15'])).
% 2.24/2.47  thf('17', plain,
% 2.24/2.47      (![X1 : $i, X3 : $i]:
% 2.24/2.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.24/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.24/2.47  thf('18', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf(t57_orders_2, axiom,
% 2.24/2.47    (![A:$i]:
% 2.24/2.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.24/2.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.24/2.47       ( ![B:$i]:
% 2.24/2.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47           ( ![C:$i]:
% 2.24/2.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47               ( ![D:$i]:
% 2.24/2.47                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 2.24/2.47                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 2.24/2.47  thf('19', plain,
% 2.24/2.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 2.24/2.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.24/2.47          | ~ (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 2.24/2.47          | (r2_hidden @ X14 @ X16)
% 2.24/2.47          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 2.24/2.47          | ~ (l1_orders_2 @ X15)
% 2.24/2.47          | ~ (v5_orders_2 @ X15)
% 2.24/2.47          | ~ (v4_orders_2 @ X15)
% 2.24/2.47          | ~ (v3_orders_2 @ X15)
% 2.24/2.47          | (v2_struct_0 @ X15))),
% 2.24/2.47      inference('cnf', [status(esa)], [t57_orders_2])).
% 2.24/2.47  thf('20', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (v3_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v4_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v5_orders_2 @ sk_A)
% 2.24/2.47          | ~ (l1_orders_2 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_hidden @ X1 @ sk_D)
% 2.24/2.47          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['18', '19'])).
% 2.24/2.47  thf('21', plain, ((v3_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('22', plain, ((v4_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('23', plain, ((v5_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('25', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_hidden @ X1 @ sk_D)
% 2.24/2.47          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 2.24/2.47  thf('26', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ X1)
% 2.24/2.47          | ~ (m1_subset_1 @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 2.24/2.47               (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_hidden @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ sk_D)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (v2_struct_0 @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['17', '25'])).
% 2.24/2.47  thf('27', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             sk_D)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('sup-', [status(thm)], ['16', '26'])).
% 2.24/2.47  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('29', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             sk_D)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('demod', [status(thm)], ['27', '28'])).
% 2.24/2.47  thf('30', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_D)
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('simplify', [status(thm)], ['29'])).
% 2.24/2.47  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('32', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             sk_D))),
% 2.24/2.47      inference('clc', [status(thm)], ['30', '31'])).
% 2.24/2.47  thf('33', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('34', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['1', '15'])).
% 2.24/2.47  thf('35', plain,
% 2.24/2.47      (![X1 : $i, X3 : $i]:
% 2.24/2.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.24/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.24/2.47  thf('36', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('37', plain,
% 2.24/2.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 2.24/2.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.24/2.47          | ~ (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 2.24/2.47          | (r2_orders_2 @ X15 @ X14 @ X17)
% 2.24/2.47          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 2.24/2.47          | ~ (l1_orders_2 @ X15)
% 2.24/2.47          | ~ (v5_orders_2 @ X15)
% 2.24/2.47          | ~ (v4_orders_2 @ X15)
% 2.24/2.47          | ~ (v3_orders_2 @ X15)
% 2.24/2.47          | (v2_struct_0 @ X15))),
% 2.24/2.47      inference('cnf', [status(esa)], [t57_orders_2])).
% 2.24/2.47  thf('38', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (v3_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v4_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v5_orders_2 @ sk_A)
% 2.24/2.47          | ~ (l1_orders_2 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 2.24/2.47          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['36', '37'])).
% 2.24/2.47  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('43', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 2.24/2.47          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 2.24/2.47  thf('44', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ X1)
% 2.24/2.47          | ~ (m1_subset_1 @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 2.24/2.47               (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ X0)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (v2_struct_0 @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['35', '43'])).
% 2.24/2.47  thf('45', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('sup-', [status(thm)], ['34', '44'])).
% 2.24/2.47  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('47', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('demod', [status(thm)], ['45', '46'])).
% 2.24/2.47  thf('48', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r2_orders_2 @ sk_A @ 
% 2.24/2.47           (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('simplify', [status(thm)], ['47'])).
% 2.24/2.47  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('50', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B))),
% 2.24/2.47      inference('clc', [status(thm)], ['48', '49'])).
% 2.24/2.47  thf('51', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['1', '15'])).
% 2.24/2.47  thf(t29_orders_2, axiom,
% 2.24/2.47    (![A:$i]:
% 2.24/2.47     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.24/2.47       ( ![B:$i]:
% 2.24/2.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47           ( ![C:$i]:
% 2.24/2.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47               ( ![D:$i]:
% 2.24/2.47                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.24/2.47                   ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 2.24/2.47                       ( r2_orders_2 @ A @ C @ D ) ) =>
% 2.24/2.47                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 2.24/2.47  thf('52', plain,
% 2.24/2.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 2.24/2.47          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 2.24/2.47          | (r2_orders_2 @ X11 @ X10 @ X12)
% 2.24/2.47          | ~ (r2_orders_2 @ X11 @ X13 @ X12)
% 2.24/2.47          | ~ (r2_orders_2 @ X11 @ X10 @ X13)
% 2.24/2.47          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.24/2.47          | ~ (l1_orders_2 @ X11)
% 2.24/2.47          | ~ (v5_orders_2 @ X11)
% 2.24/2.47          | ~ (v4_orders_2 @ X11))),
% 2.24/2.47      inference('cnf', [status(esa)], [t29_orders_2])).
% 2.24/2.47  thf('53', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | ~ (v4_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v5_orders_2 @ sk_A)
% 2.24/2.47          | ~ (l1_orders_2 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ 
% 2.24/2.47               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ X1 @ X2)
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X2)
% 2.24/2.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['51', '52'])).
% 2.24/2.47  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('57', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ 
% 2.24/2.47               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ X1 @ X2)
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X2)
% 2.24/2.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 2.24/2.47  thf('58', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ sk_B @ X1)
% 2.24/2.47          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('sup-', [status(thm)], ['50', '57'])).
% 2.24/2.47  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('60', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ sk_B @ X1)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('demod', [status(thm)], ['58', '59'])).
% 2.24/2.47  thf('61', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         (~ (r2_orders_2 @ sk_A @ sk_B @ X1)
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('simplify', [status(thm)], ['60'])).
% 2.24/2.47  thf('62', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_C_1)
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 2.24/2.47      inference('sup-', [status(thm)], ['33', '61'])).
% 2.24/2.47  thf('63', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('64', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (r2_orders_2 @ sk_A @ 
% 2.24/2.47             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_C_1))),
% 2.24/2.47      inference('demod', [status(thm)], ['62', '63'])).
% 2.24/2.47  thf('65', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['1', '15'])).
% 2.24/2.47  thf('66', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('67', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('68', plain,
% 2.24/2.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 2.24/2.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.24/2.47          | ~ (r2_orders_2 @ X15 @ X14 @ X17)
% 2.24/2.47          | ~ (r2_hidden @ X14 @ X16)
% 2.24/2.47          | (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 2.24/2.47          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 2.24/2.47          | ~ (l1_orders_2 @ X15)
% 2.24/2.47          | ~ (v5_orders_2 @ X15)
% 2.24/2.47          | ~ (v4_orders_2 @ X15)
% 2.24/2.47          | ~ (v3_orders_2 @ X15)
% 2.24/2.47          | (v2_struct_0 @ X15))),
% 2.24/2.47      inference('cnf', [status(esa)], [t57_orders_2])).
% 2.24/2.47  thf('69', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (v3_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v4_orders_2 @ sk_A)
% 2.24/2.47          | ~ (v5_orders_2 @ sk_A)
% 2.24/2.47          | ~ (l1_orders_2 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.24/2.47          | ~ (r2_hidden @ X1 @ sk_D)
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['67', '68'])).
% 2.24/2.47  thf('70', plain, ((v3_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('71', plain, ((v4_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('72', plain, ((v5_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('74', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i]:
% 2.24/2.47         ((v2_struct_0 @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.24/2.47          | ~ (r2_hidden @ X1 @ sk_D)
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 2.24/2.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 2.24/2.47  thf('75', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C_1)
% 2.24/2.47          | ~ (r2_hidden @ X0 @ sk_D)
% 2.24/2.47          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.24/2.47          | (v2_struct_0 @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['66', '74'])).
% 2.24/2.47  thf('76', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.24/2.47          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47               sk_D)
% 2.24/2.47          | ~ (r2_orders_2 @ sk_A @ 
% 2.24/2.47               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_C_1))),
% 2.24/2.47      inference('sup-', [status(thm)], ['65', '75'])).
% 2.24/2.47  thf('77', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47               sk_D)
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.24/2.47          | (v2_struct_0 @ sk_A)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('sup-', [status(thm)], ['64', '76'])).
% 2.24/2.47  thf('78', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((v2_struct_0 @ sk_A)
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.24/2.47          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47               sk_D)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('simplify', [status(thm)], ['77'])).
% 2.24/2.47  thf('79', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.24/2.47          | (v2_struct_0 @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['32', '78'])).
% 2.24/2.47  thf('80', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((v2_struct_0 @ sk_A)
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.24/2.47          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.24/2.47      inference('simplify', [status(thm)], ['79'])).
% 2.24/2.47  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('82', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.24/2.47          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.24/2.47             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1)))),
% 2.24/2.47      inference('clc', [status(thm)], ['80', '81'])).
% 2.24/2.47  thf('83', plain,
% 2.24/2.47      (![X1 : $i, X3 : $i]:
% 2.24/2.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.24/2.47      inference('cnf', [status(esa)], [d3_tarski])).
% 2.24/2.47  thf('84', plain,
% 2.24/2.47      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 2.24/2.47         (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.24/2.47        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 2.24/2.47           (k3_orders_2 @ sk_A @ sk_D @ sk_C_1)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['82', '83'])).
% 2.24/2.47  thf('85', plain,
% 2.24/2.47      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 2.24/2.47        (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))),
% 2.24/2.47      inference('simplify', [status(thm)], ['84'])).
% 2.24/2.47  thf('86', plain, ($false), inference('demod', [status(thm)], ['0', '85'])).
% 2.24/2.47  
% 2.24/2.47  % SZS output end Refutation
% 2.24/2.47  
% 2.24/2.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
