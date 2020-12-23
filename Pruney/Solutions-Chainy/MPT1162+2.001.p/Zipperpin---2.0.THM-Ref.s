%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S2gvXJWdCd

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:03 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 327 expanded)
%              Number of leaves         :   25 ( 106 expanded)
%              Depth                    :   28
%              Number of atoms          : 1568 (6979 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_orders_2 @ X18 @ X19 @ X20 ) )
      | ( r2_hidden @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_orders_2 @ X18 @ X19 @ X20 ) )
      | ( r2_orders_2 @ X18 @ X17 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_orders_2 @ X8 @ X7 @ X9 )
      | ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

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

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r2_orders_2 @ X14 @ X13 @ X15 )
      | ~ ( r2_orders_2 @ X14 @ X16 @ X15 )
      | ~ ( r1_orders_2 @ X14 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t32_orders_2])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X2 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X2 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','70'])).

thf('72',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r2_orders_2 @ X18 @ X17 @ X20 )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ( r2_hidden @ X17 @ ( k3_orders_2 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('78',plain,(
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
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ sk_D )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
      | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,
    ( ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) )
    | ( r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['0','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S2gvXJWdCd
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.97/2.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.97/2.23  % Solved by: fo/fo7.sh
% 1.97/2.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.23  % done 1203 iterations in 1.756s
% 1.97/2.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.97/2.23  % SZS output start Refutation
% 1.97/2.23  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.97/2.23  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.97/2.23  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.97/2.23  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.97/2.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.97/2.23  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 1.97/2.23  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.23  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.97/2.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.23  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.97/2.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.97/2.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.23  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.23  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 1.97/2.23  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.97/2.23  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.97/2.23  thf(sk_D_type, type, sk_D: $i).
% 1.97/2.23  thf(t64_orders_2, conjecture,
% 1.97/2.23    (![A:$i]:
% 1.97/2.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.97/2.23         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.97/2.23       ( ![B:$i]:
% 1.97/2.23         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.97/2.23           ( ![C:$i]:
% 1.97/2.23             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.97/2.23               ( ![D:$i]:
% 1.97/2.23                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.23                   ( ( r2_orders_2 @ A @ B @ C ) =>
% 1.97/2.23                     ( r1_tarski @
% 1.97/2.23                       ( k3_orders_2 @ A @ D @ B ) @ 
% 1.97/2.23                       ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 1.97/2.23  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.23    (~( ![A:$i]:
% 1.97/2.23        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.97/2.23            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.97/2.23          ( ![B:$i]:
% 1.97/2.23            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.97/2.23              ( ![C:$i]:
% 1.97/2.23                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.97/2.23                  ( ![D:$i]:
% 1.97/2.23                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.23                      ( ( r2_orders_2 @ A @ B @ C ) =>
% 1.97/2.23                        ( r1_tarski @
% 1.97/2.23                          ( k3_orders_2 @ A @ D @ B ) @ 
% 1.97/2.23                          ( k3_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 1.97/2.23    inference('cnf.neg', [status(esa)], [t64_orders_2])).
% 1.97/2.23  thf('0', plain,
% 1.97/2.23      (~ (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 1.97/2.23          (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf(d3_tarski, axiom,
% 1.97/2.23    (![A:$i,B:$i]:
% 1.97/2.23     ( ( r1_tarski @ A @ B ) <=>
% 1.97/2.23       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.97/2.23  thf('1', plain,
% 1.97/2.23      (![X1 : $i, X3 : $i]:
% 1.97/2.23         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.97/2.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.97/2.23  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf('3', plain,
% 1.97/2.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf(dt_k3_orders_2, axiom,
% 1.97/2.23    (![A:$i,B:$i,C:$i]:
% 1.97/2.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.97/2.23         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 1.97/2.23         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.97/2.23         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.23       ( m1_subset_1 @
% 1.97/2.23         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.97/2.23  thf('4', plain,
% 1.97/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.97/2.23         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.97/2.23          | ~ (l1_orders_2 @ X11)
% 1.97/2.23          | ~ (v5_orders_2 @ X11)
% 1.97/2.23          | ~ (v4_orders_2 @ X11)
% 1.97/2.23          | ~ (v3_orders_2 @ X11)
% 1.97/2.23          | (v2_struct_0 @ X11)
% 1.97/2.23          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 1.97/2.23          | (m1_subset_1 @ (k3_orders_2 @ X11 @ X10 @ X12) @ 
% 1.97/2.23             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 1.97/2.23      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 1.97/2.23  thf('5', plain,
% 1.97/2.23      (![X0 : $i]:
% 1.97/2.23         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 1.97/2.23           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.97/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.97/2.23          | (v2_struct_0 @ sk_A)
% 1.97/2.23          | ~ (v3_orders_2 @ sk_A)
% 1.97/2.23          | ~ (v4_orders_2 @ sk_A)
% 1.97/2.23          | ~ (v5_orders_2 @ sk_A)
% 1.97/2.23          | ~ (l1_orders_2 @ sk_A))),
% 1.97/2.23      inference('sup-', [status(thm)], ['3', '4'])).
% 1.97/2.23  thf('6', plain, ((v3_orders_2 @ sk_A)),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf('7', plain, ((v4_orders_2 @ sk_A)),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf('8', plain, ((v5_orders_2 @ sk_A)),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf('10', plain,
% 1.97/2.23      (![X0 : $i]:
% 1.97/2.23         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 1.97/2.23           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.97/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.97/2.23          | (v2_struct_0 @ sk_A))),
% 1.97/2.23      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 1.97/2.23  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf('12', plain,
% 1.97/2.23      (![X0 : $i]:
% 1.97/2.23         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.97/2.23          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 1.97/2.23             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.97/2.23      inference('clc', [status(thm)], ['10', '11'])).
% 1.97/2.23  thf('13', plain,
% 1.97/2.23      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 1.97/2.23        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.23      inference('sup-', [status(thm)], ['2', '12'])).
% 1.97/2.23  thf(t4_subset, axiom,
% 1.97/2.23    (![A:$i,B:$i,C:$i]:
% 1.97/2.23     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.97/2.23       ( m1_subset_1 @ A @ C ) ))).
% 1.97/2.23  thf('14', plain,
% 1.97/2.23      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.97/2.23         (~ (r2_hidden @ X4 @ X5)
% 1.97/2.23          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.97/2.23          | (m1_subset_1 @ X4 @ X6))),
% 1.97/2.23      inference('cnf', [status(esa)], [t4_subset])).
% 1.97/2.23  thf('15', plain,
% 1.97/2.23      (![X0 : $i]:
% 1.97/2.23         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.97/2.23          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 1.97/2.23      inference('sup-', [status(thm)], ['13', '14'])).
% 1.97/2.23  thf('16', plain,
% 1.97/2.23      (![X0 : $i]:
% 1.97/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 1.97/2.23          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 1.97/2.23             (u1_struct_0 @ sk_A)))),
% 1.97/2.23      inference('sup-', [status(thm)], ['1', '15'])).
% 1.97/2.23  thf('17', plain,
% 1.97/2.23      (![X1 : $i, X3 : $i]:
% 1.97/2.23         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.97/2.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.97/2.23  thf('18', plain,
% 1.97/2.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.23  thf(t57_orders_2, axiom,
% 1.97/2.23    (![A:$i]:
% 1.97/2.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.97/2.23         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.97/2.23       ( ![B:$i]:
% 1.97/2.23         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.97/2.23           ( ![C:$i]:
% 1.97/2.23             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.97/2.23               ( ![D:$i]:
% 1.97/2.23                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.23                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 1.97/2.23                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 1.97/2.23  thf('19', plain,
% 1.97/2.23      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.97/2.23         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 1.97/2.23          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.97/2.23          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 1.97/2.23          | (r2_hidden @ X17 @ X19)
% 1.97/2.23          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 1.97/2.23          | ~ (l1_orders_2 @ X18)
% 1.97/2.23          | ~ (v5_orders_2 @ X18)
% 1.97/2.23          | ~ (v4_orders_2 @ X18)
% 1.97/2.23          | ~ (v3_orders_2 @ X18)
% 1.97/2.23          | (v2_struct_0 @ X18))),
% 1.97/2.23      inference('cnf', [status(esa)], [t57_orders_2])).
% 1.97/2.23  thf('20', plain,
% 1.97/2.23      (![X0 : $i, X1 : $i]:
% 1.97/2.23         ((v2_struct_0 @ sk_A)
% 1.97/2.23          | ~ (v3_orders_2 @ sk_A)
% 1.97/2.23          | ~ (v4_orders_2 @ sk_A)
% 2.06/2.23          | ~ (v5_orders_2 @ sk_A)
% 2.06/2.23          | ~ (l1_orders_2 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_hidden @ X1 @ sk_D)
% 2.06/2.23          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['18', '19'])).
% 2.06/2.23  thf('21', plain, ((v3_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('22', plain, ((v4_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('23', plain, ((v5_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('25', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((v2_struct_0 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_hidden @ X1 @ sk_D)
% 2.06/2.23          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 2.06/2.23  thf('26', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ X1)
% 2.06/2.23          | ~ (m1_subset_1 @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 2.06/2.23               (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_hidden @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ sk_D)
% 2.06/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (v2_struct_0 @ sk_A))),
% 2.06/2.23      inference('sup-', [status(thm)], ['17', '25'])).
% 2.06/2.23  thf('27', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (v2_struct_0 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             sk_D)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('sup-', [status(thm)], ['16', '26'])).
% 2.06/2.23  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('29', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (v2_struct_0 @ sk_A)
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             sk_D)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('demod', [status(thm)], ['27', '28'])).
% 2.06/2.23  thf('30', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_D)
% 2.06/2.23          | (v2_struct_0 @ sk_A)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('simplify', [status(thm)], ['29'])).
% 2.06/2.23  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('32', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             sk_D))),
% 2.06/2.23      inference('clc', [status(thm)], ['30', '31'])).
% 2.06/2.23  thf('33', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('34', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['1', '15'])).
% 2.06/2.23  thf('35', plain,
% 2.06/2.23      (![X1 : $i, X3 : $i]:
% 2.06/2.23         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.06/2.23      inference('cnf', [status(esa)], [d3_tarski])).
% 2.06/2.23  thf('36', plain,
% 2.06/2.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('37', plain,
% 2.06/2.23      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.06/2.23         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.06/2.23          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.06/2.23          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 2.06/2.23          | (r2_orders_2 @ X18 @ X17 @ X20)
% 2.06/2.23          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 2.06/2.23          | ~ (l1_orders_2 @ X18)
% 2.06/2.23          | ~ (v5_orders_2 @ X18)
% 2.06/2.23          | ~ (v4_orders_2 @ X18)
% 2.06/2.23          | ~ (v3_orders_2 @ X18)
% 2.06/2.23          | (v2_struct_0 @ X18))),
% 2.06/2.23      inference('cnf', [status(esa)], [t57_orders_2])).
% 2.06/2.23  thf('38', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((v2_struct_0 @ sk_A)
% 2.06/2.23          | ~ (v3_orders_2 @ sk_A)
% 2.06/2.23          | ~ (v4_orders_2 @ sk_A)
% 2.06/2.23          | ~ (v5_orders_2 @ sk_A)
% 2.06/2.23          | ~ (l1_orders_2 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 2.06/2.23          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['36', '37'])).
% 2.06/2.23  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('43', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((v2_struct_0 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 2.06/2.23          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 2.06/2.23  thf('44', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ X1)
% 2.06/2.23          | ~ (m1_subset_1 @ (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 2.06/2.23               (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ X0)
% 2.06/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (v2_struct_0 @ sk_A))),
% 2.06/2.23      inference('sup-', [status(thm)], ['35', '43'])).
% 2.06/2.23  thf('45', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (v2_struct_0 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('sup-', [status(thm)], ['34', '44'])).
% 2.06/2.23  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('47', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (v2_struct_0 @ sk_A)
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('demod', [status(thm)], ['45', '46'])).
% 2.06/2.23  thf('48', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r2_orders_2 @ sk_A @ 
% 2.06/2.23           (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.06/2.23          | (v2_struct_0 @ sk_A)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('simplify', [status(thm)], ['47'])).
% 2.06/2.23  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('50', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B))),
% 2.06/2.23      inference('clc', [status(thm)], ['48', '49'])).
% 2.06/2.23  thf('51', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['1', '15'])).
% 2.06/2.23  thf(d10_orders_2, axiom,
% 2.06/2.23    (![A:$i]:
% 2.06/2.23     ( ( l1_orders_2 @ A ) =>
% 2.06/2.23       ( ![B:$i]:
% 2.06/2.23         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.06/2.23           ( ![C:$i]:
% 2.06/2.23             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.06/2.23               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 2.06/2.23                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 2.06/2.23  thf('52', plain,
% 2.06/2.23      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.06/2.23         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 2.06/2.23          | ~ (r2_orders_2 @ X8 @ X7 @ X9)
% 2.06/2.23          | (r1_orders_2 @ X8 @ X7 @ X9)
% 2.06/2.23          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 2.06/2.23          | ~ (l1_orders_2 @ X8))),
% 2.06/2.23      inference('cnf', [status(esa)], [d10_orders_2])).
% 2.06/2.23  thf('53', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | ~ (l1_orders_2 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r1_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ 
% 2.06/2.23               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1))),
% 2.06/2.23      inference('sup-', [status(thm)], ['51', '52'])).
% 2.06/2.23  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('55', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r1_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ 
% 2.06/2.23               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1))),
% 2.06/2.23      inference('demod', [status(thm)], ['53', '54'])).
% 2.06/2.23  thf('56', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r1_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.06/2.23          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('sup-', [status(thm)], ['50', '55'])).
% 2.06/2.23  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('58', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r1_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('demod', [status(thm)], ['56', '57'])).
% 2.06/2.23  thf('59', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_orders_2 @ sk_A @ 
% 2.06/2.23           (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_B)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('simplify', [status(thm)], ['58'])).
% 2.06/2.23  thf('60', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['1', '15'])).
% 2.06/2.23  thf(t32_orders_2, axiom,
% 2.06/2.23    (![A:$i]:
% 2.06/2.23     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.06/2.23       ( ![B:$i]:
% 2.06/2.23         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.06/2.23           ( ![C:$i]:
% 2.06/2.23             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.06/2.23               ( ![D:$i]:
% 2.06/2.23                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.06/2.23                   ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 2.06/2.23                         ( r1_orders_2 @ A @ C @ D ) ) | 
% 2.06/2.23                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 2.06/2.23                         ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 2.06/2.23                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 2.06/2.23  thf('61', plain,
% 2.06/2.23      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.06/2.23         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 2.06/2.23          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 2.06/2.23          | (r2_orders_2 @ X14 @ X13 @ X15)
% 2.06/2.23          | ~ (r2_orders_2 @ X14 @ X16 @ X15)
% 2.06/2.23          | ~ (r1_orders_2 @ X14 @ X13 @ X16)
% 2.06/2.23          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 2.06/2.23          | ~ (l1_orders_2 @ X14)
% 2.06/2.23          | ~ (v5_orders_2 @ X14)
% 2.06/2.23          | ~ (v4_orders_2 @ X14))),
% 2.06/2.23      inference('cnf', [status(esa)], [t32_orders_2])).
% 2.06/2.23  thf('62', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | ~ (v4_orders_2 @ sk_A)
% 2.06/2.23          | ~ (v5_orders_2 @ sk_A)
% 2.06/2.23          | ~ (l1_orders_2 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | ~ (r1_orders_2 @ sk_A @ 
% 2.06/2.23               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ X1 @ X2)
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X2)
% 2.06/2.23          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['60', '61'])).
% 2.06/2.23  thf('63', plain, ((v4_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('64', plain, ((v5_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('66', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | ~ (r1_orders_2 @ sk_A @ 
% 2.06/2.23               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ X1 @ X2)
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X2)
% 2.06/2.23          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 2.06/2.23  thf('67', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ sk_B @ X1)
% 2.06/2.23          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('sup-', [status(thm)], ['59', '66'])).
% 2.06/2.23  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('69', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ sk_B @ X1)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('demod', [status(thm)], ['67', '68'])).
% 2.06/2.23  thf('70', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         (~ (r2_orders_2 @ sk_A @ sk_B @ X1)
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ X1)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('simplify', [status(thm)], ['69'])).
% 2.06/2.23  thf('71', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_C_1)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 2.06/2.23      inference('sup-', [status(thm)], ['33', '70'])).
% 2.06/2.23  thf('72', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('73', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r2_orders_2 @ sk_A @ 
% 2.06/2.23             (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_C_1))),
% 2.06/2.23      inference('demod', [status(thm)], ['71', '72'])).
% 2.06/2.23  thf('74', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (m1_subset_1 @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['1', '15'])).
% 2.06/2.23  thf('75', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('76', plain,
% 2.06/2.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('77', plain,
% 2.06/2.23      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.06/2.23         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.06/2.23          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.06/2.23          | ~ (r2_orders_2 @ X18 @ X17 @ X20)
% 2.06/2.23          | ~ (r2_hidden @ X17 @ X19)
% 2.06/2.23          | (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 2.06/2.23          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 2.06/2.23          | ~ (l1_orders_2 @ X18)
% 2.06/2.23          | ~ (v5_orders_2 @ X18)
% 2.06/2.23          | ~ (v4_orders_2 @ X18)
% 2.06/2.23          | ~ (v3_orders_2 @ X18)
% 2.06/2.23          | (v2_struct_0 @ X18))),
% 2.06/2.23      inference('cnf', [status(esa)], [t57_orders_2])).
% 2.06/2.23  thf('78', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((v2_struct_0 @ sk_A)
% 2.06/2.23          | ~ (v3_orders_2 @ sk_A)
% 2.06/2.23          | ~ (v4_orders_2 @ sk_A)
% 2.06/2.23          | ~ (v5_orders_2 @ sk_A)
% 2.06/2.23          | ~ (l1_orders_2 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.06/2.23          | ~ (r2_hidden @ X1 @ sk_D)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['76', '77'])).
% 2.06/2.23  thf('79', plain, ((v3_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('80', plain, ((v4_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('81', plain, ((v5_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('83', plain,
% 2.06/2.23      (![X0 : $i, X1 : $i]:
% 2.06/2.23         ((v2_struct_0 @ sk_A)
% 2.06/2.23          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 2.06/2.23          | ~ (r2_hidden @ X1 @ sk_D)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ X1 @ X0)
% 2.06/2.23          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.06/2.23      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 2.06/2.23  thf('84', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C_1)
% 2.06/2.23          | ~ (r2_hidden @ X0 @ sk_D)
% 2.06/2.23          | (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.06/2.23          | (v2_struct_0 @ sk_A))),
% 2.06/2.23      inference('sup-', [status(thm)], ['75', '83'])).
% 2.06/2.23  thf('85', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (v2_struct_0 @ sk_A)
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.06/2.23          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23               sk_D)
% 2.06/2.23          | ~ (r2_orders_2 @ sk_A @ 
% 2.06/2.23               (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ sk_C_1))),
% 2.06/2.23      inference('sup-', [status(thm)], ['74', '84'])).
% 2.06/2.23  thf('86', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23               sk_D)
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.06/2.23          | (v2_struct_0 @ sk_A)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('sup-', [status(thm)], ['73', '85'])).
% 2.06/2.23  thf('87', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((v2_struct_0 @ sk_A)
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.06/2.23          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23               sk_D)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('simplify', [status(thm)], ['86'])).
% 2.06/2.23  thf('88', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.06/2.23          | (v2_struct_0 @ sk_A))),
% 2.06/2.23      inference('sup-', [status(thm)], ['32', '87'])).
% 2.06/2.23  thf('89', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((v2_struct_0 @ sk_A)
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.06/2.23          | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0))),
% 2.06/2.23      inference('simplify', [status(thm)], ['88'])).
% 2.06/2.23  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 2.06/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.23  thf('91', plain,
% 2.06/2.23      (![X0 : $i]:
% 2.06/2.23         ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ X0)
% 2.06/2.23          | (r2_hidden @ (sk_C @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B)) @ 
% 2.06/2.23             (k3_orders_2 @ sk_A @ sk_D @ sk_C_1)))),
% 2.06/2.23      inference('clc', [status(thm)], ['89', '90'])).
% 2.06/2.23  thf('92', plain,
% 2.06/2.23      (![X1 : $i, X3 : $i]:
% 2.06/2.23         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.06/2.23      inference('cnf', [status(esa)], [d3_tarski])).
% 2.06/2.23  thf('93', plain,
% 2.06/2.23      (((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 2.06/2.23         (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))
% 2.06/2.23        | (r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 2.06/2.23           (k3_orders_2 @ sk_A @ sk_D @ sk_C_1)))),
% 2.06/2.23      inference('sup-', [status(thm)], ['91', '92'])).
% 2.06/2.23  thf('94', plain,
% 2.06/2.23      ((r1_tarski @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 2.06/2.23        (k3_orders_2 @ sk_A @ sk_D @ sk_C_1))),
% 2.06/2.23      inference('simplify', [status(thm)], ['93'])).
% 2.06/2.23  thf('95', plain, ($false), inference('demod', [status(thm)], ['0', '94'])).
% 2.06/2.23  
% 2.06/2.23  % SZS output end Refutation
% 2.06/2.23  
% 2.06/2.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
