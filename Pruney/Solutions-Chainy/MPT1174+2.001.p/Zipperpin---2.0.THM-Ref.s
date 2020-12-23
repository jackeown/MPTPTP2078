%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L4cA2ROVjh

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:09 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 859 expanded)
%              Number of leaves         :   33 ( 265 expanded)
%              Depth                    :   24
%              Number of atoms          : 1533 (18570 expanded)
%              Number of equality atoms :   24 ( 854 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t81_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ C )
                 => ( ( B
                      = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) )
                   => ( ( k3_orders_2 @ A @ D @ B )
                      = k1_xboole_0 ) ) ) ) ) ) )).

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
                ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ C )
                   => ( ( B
                        = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) )
                     => ( ( k3_orders_2 @ A @ D @ B )
                        = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_orders_2 @ X3 @ X2 @ X4 )
      | ( X2 != X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ~ ( r2_orders_2 @ X3 @ X4 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_orders_1 @ sk_C_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_orders_1 @ X9 @ ( k1_orders_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m2_orders_2 @ X10 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

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

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
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
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('30',plain,
    ( ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

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

thf('34',plain,(
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

thf('35',plain,(
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
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('44',plain,
    ( ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r1_orders_2 @ X15 @ X16 @ X14 )
      | ( X14 = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['48','49'])).

thf('60',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('61',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_orders_2 @ X3 @ X2 @ X4 )
      | ( r1_orders_2 @ X3 @ X2 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','67'])).

thf('69',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('71',plain,(
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

thf('72',plain,(
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
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('85',plain,
    ( sk_B
    = ( k1_funct_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_orders_2,axiom,(
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
                  ( ( m1_orders_1 @ D @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m2_orders_2 @ E @ A @ D )
                     => ( ( ( r2_hidden @ B @ E )
                          & ( C
                            = ( k1_funct_1 @ D @ ( u1_struct_0 @ A ) ) ) )
                       => ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_orders_1 @ X23 @ ( k1_orders_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( X24
       != ( k1_funct_1 @ X23 @ ( u1_struct_0 @ X22 ) ) )
      | ( r3_orders_2 @ X22 @ X24 @ X21 )
      | ~ ( r2_hidden @ X21 @ X25 )
      | ~ ( m2_orders_2 @ X25 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t80_orders_2])).

thf('87',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X23 @ ( u1_struct_0 @ X22 ) ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m2_orders_2 @ X25 @ X22 @ X23 )
      | ~ ( r2_hidden @ X21 @ X25 )
      | ( r3_orders_2 @ X22 @ ( k1_funct_1 @ X23 @ ( u1_struct_0 @ X22 ) ) @ X21 )
      | ~ ( m1_orders_1 @ X23 @ ( k1_orders_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_orders_1 @ sk_C_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r3_orders_2 @ sk_A @ ( k1_funct_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_C_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_orders_1 @ sk_C_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( sk_B
    = ( k1_funct_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['84','96'])).

thf('98',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m2_orders_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','97'])).

thf('99',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('104',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ~ ( r3_orders_2 @ X12 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,
    ( sk_B
    = ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','113'])).

thf('115',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['50','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['5','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L4cA2ROVjh
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:13:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 134 iterations in 0.195s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.66  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.47/0.66  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.66  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.47/0.66  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.47/0.66  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.66  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.66  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.47/0.66  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.47/0.66  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.47/0.66  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.47/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.66  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.47/0.66  thf(t81_orders_2, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66               ( ![D:$i]:
% 0.47/0.66                 ( ( m2_orders_2 @ D @ A @ C ) =>
% 0.47/0.66                   ( ( ( B ) = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66                     ( ( k3_orders_2 @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.66            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.66          ( ![B:$i]:
% 0.47/0.66            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66              ( ![C:$i]:
% 0.47/0.66                ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66                  ( ![D:$i]:
% 0.47/0.66                    ( ( m2_orders_2 @ D @ A @ C ) =>
% 0.47/0.66                      ( ( ( B ) = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66                        ( ( k3_orders_2 @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t81_orders_2])).
% 0.47/0.66  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d10_orders_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_orders_2 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.47/0.66                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.47/0.66          | ~ (r2_orders_2 @ X3 @ X2 @ X4)
% 0.47/0.66          | ((X2) != (X4))
% 0.47/0.66          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.47/0.66          | ~ (l1_orders_2 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X3 : $i, X4 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ X3)
% 0.47/0.66          | ~ (r2_orders_2 @ X3 @ X4 @ X4)
% 0.47/0.66          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_B) | ~ (l1_orders_2 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['0', '2'])).
% 0.47/0.66  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('5', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.47/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.66  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('7', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      ((m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(dt_m2_orders_2, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.47/0.66         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.66       ( ![C:$i]:
% 0.47/0.66         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.47/0.66           ( ( v6_orders_2 @ C @ A ) & 
% 0.47/0.66             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         (~ (l1_orders_2 @ X8)
% 0.47/0.66          | ~ (v5_orders_2 @ X8)
% 0.47/0.66          | ~ (v4_orders_2 @ X8)
% 0.47/0.66          | ~ (v3_orders_2 @ X8)
% 0.47/0.66          | (v2_struct_0 @ X8)
% 0.47/0.66          | ~ (m1_orders_1 @ X9 @ (k1_orders_1 @ (u1_struct_0 @ X8)))
% 0.47/0.66          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.47/0.66          | ~ (m2_orders_2 @ X10 @ X8 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.47/0.66          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v3_orders_2 @ sk_A)
% 0.47/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.47/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain, ((v3_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('12', plain, ((v4_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.47/0.66          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.47/0.66  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1))),
% 0.47/0.66      inference('clc', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['7', '17'])).
% 0.47/0.66  thf(dt_k3_orders_2, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.47/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.47/0.66         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66       ( m1_subset_1 @
% 0.47/0.66         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.47/0.66          | ~ (l1_orders_2 @ X6)
% 0.47/0.66          | ~ (v5_orders_2 @ X6)
% 0.47/0.66          | ~ (v4_orders_2 @ X6)
% 0.47/0.66          | ~ (v3_orders_2 @ X6)
% 0.47/0.66          | (v2_struct_0 @ X6)
% 0.47/0.66          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.47/0.66          | (m1_subset_1 @ (k3_orders_2 @ X6 @ X5 @ X7) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v3_orders_2 @ sk_A)
% 0.47/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.47/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain, ((v3_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('22', plain, ((v4_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('23', plain, ((v5_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.47/0.66  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('clc', [status(thm)], ['25', '26'])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.47/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '27'])).
% 0.47/0.66  thf(t10_subset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.66       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66            ( ![C:$i]:
% 0.47/0.66              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.47/0.66          | ((X0) = (k1_xboole_0))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      ((((k3_orders_2 @ sk_A @ sk_D @ sk_B) = (k1_xboole_0))
% 0.47/0.66        | (r2_hidden @ 
% 0.47/0.66           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.66           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('31', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      ((r2_hidden @ 
% 0.47/0.66        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.66        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['7', '17'])).
% 0.47/0.66  thf(t57_orders_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66               ( ![D:$i]:
% 0.47/0.66                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.47/0.66                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.47/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.66          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 0.47/0.66          | (r2_orders_2 @ X18 @ X17 @ X20)
% 0.47/0.66          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.47/0.66          | ~ (l1_orders_2 @ X18)
% 0.47/0.66          | ~ (v5_orders_2 @ X18)
% 0.47/0.66          | ~ (v4_orders_2 @ X18)
% 0.47/0.66          | ~ (v3_orders_2 @ X18)
% 0.47/0.66          | (v2_struct_0 @ X18))),
% 0.47/0.66      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v3_orders_2 @ sk_A)
% 0.47/0.66          | ~ (v4_orders_2 @ sk_A)
% 0.47/0.66          | ~ (v5_orders_2 @ sk_A)
% 0.47/0.66          | ~ (l1_orders_2 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.47/0.66          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((v2_struct_0 @ sk_A)
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.47/0.67          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      ((~ (m1_subset_1 @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67           (u1_struct_0 @ sk_A))
% 0.47/0.67        | (r2_orders_2 @ sk_A @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67           sk_B)
% 0.47/0.67        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.67        | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['32', '40'])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.47/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['6', '27'])).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.47/0.67          | ((X0) = (k1_xboole_0))
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      ((((k3_orders_2 @ sk_A @ sk_D @ sk_B) = (k1_xboole_0))
% 0.47/0.67        | (m1_subset_1 @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67           (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.67  thf('45', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('46', plain,
% 0.47/0.67      ((m1_subset_1 @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.47/0.67  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      (((r2_orders_2 @ sk_A @ 
% 0.47/0.67         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67         sk_B)
% 0.47/0.67        | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['41', '46', '47'])).
% 0.47/0.67  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      ((r2_orders_2 @ sk_A @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        sk_B)),
% 0.47/0.67      inference('clc', [status(thm)], ['48', '49'])).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      ((m1_subset_1 @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.47/0.67  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(t25_orders_2, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.67           ( ![C:$i]:
% 0.47/0.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.67               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.47/0.67                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.47/0.67  thf('53', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.47/0.67          | ~ (r1_orders_2 @ X15 @ X14 @ X16)
% 0.47/0.67          | ~ (r1_orders_2 @ X15 @ X16 @ X14)
% 0.47/0.67          | ((X14) = (X16))
% 0.47/0.67          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.47/0.67          | ~ (l1_orders_2 @ X15)
% 0.47/0.67          | ~ (v5_orders_2 @ X15))),
% 0.47/0.67      inference('cnf', [status(esa)], [t25_orders_2])).
% 0.47/0.67  thf('54', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v5_orders_2 @ sk_A)
% 0.47/0.67          | ~ (l1_orders_2 @ sk_A)
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | ((sk_B) = (X0))
% 0.47/0.67          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.47/0.67          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.67  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | ((sk_B) = (X0))
% 0.47/0.67          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.47/0.67          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.47/0.67      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.47/0.67  thf('58', plain,
% 0.47/0.67      ((~ (r1_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.47/0.67        | ~ (r1_orders_2 @ sk_A @ 
% 0.47/0.67             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67             sk_B)
% 0.47/0.67        | ((sk_B)
% 0.47/0.67            = (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['51', '57'])).
% 0.47/0.67  thf('59', plain,
% 0.47/0.67      ((r2_orders_2 @ sk_A @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        sk_B)),
% 0.47/0.67      inference('clc', [status(thm)], ['48', '49'])).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      ((m1_subset_1 @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.47/0.67  thf('61', plain,
% 0.47/0.67      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.47/0.67          | ~ (r2_orders_2 @ X3 @ X2 @ X4)
% 0.47/0.67          | (r1_orders_2 @ X3 @ X2 @ X4)
% 0.47/0.67          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.47/0.67          | ~ (l1_orders_2 @ X3))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.47/0.67  thf('62', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (l1_orders_2 @ sk_A)
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | (r1_orders_2 @ sk_A @ 
% 0.47/0.67             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67             X0)
% 0.47/0.67          | ~ (r2_orders_2 @ sk_A @ 
% 0.47/0.67               (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.47/0.67                (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67               X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.67  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | (r1_orders_2 @ sk_A @ 
% 0.47/0.67             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67             X0)
% 0.47/0.67          | ~ (r2_orders_2 @ sk_A @ 
% 0.47/0.67               (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.47/0.67                (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67               X0))),
% 0.47/0.67      inference('demod', [status(thm)], ['62', '63'])).
% 0.47/0.67  thf('65', plain,
% 0.47/0.67      (((r1_orders_2 @ sk_A @ 
% 0.47/0.67         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67         sk_B)
% 0.47/0.67        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['59', '64'])).
% 0.47/0.67  thf('66', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('67', plain,
% 0.47/0.67      ((r1_orders_2 @ sk_A @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        sk_B)),
% 0.47/0.67      inference('demod', [status(thm)], ['65', '66'])).
% 0.47/0.67  thf('68', plain,
% 0.47/0.67      ((~ (r1_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.47/0.67        | ((sk_B)
% 0.47/0.67            = (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['58', '67'])).
% 0.47/0.67  thf('69', plain,
% 0.47/0.67      ((r2_hidden @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.47/0.67  thf('70', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['7', '17'])).
% 0.47/0.67  thf('71', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.47/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.67          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 0.47/0.67          | (r2_hidden @ X17 @ X19)
% 0.47/0.67          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.47/0.67          | ~ (l1_orders_2 @ X18)
% 0.47/0.67          | ~ (v5_orders_2 @ X18)
% 0.47/0.67          | ~ (v4_orders_2 @ X18)
% 0.47/0.67          | ~ (v3_orders_2 @ X18)
% 0.47/0.67          | (v2_struct_0 @ X18))),
% 0.47/0.67      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.47/0.67  thf('72', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((v2_struct_0 @ sk_A)
% 0.47/0.67          | ~ (v3_orders_2 @ sk_A)
% 0.47/0.67          | ~ (v4_orders_2 @ sk_A)
% 0.47/0.67          | ~ (v5_orders_2 @ sk_A)
% 0.47/0.67          | ~ (l1_orders_2 @ sk_A)
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | (r2_hidden @ X1 @ sk_D)
% 0.47/0.67          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['70', '71'])).
% 0.47/0.67  thf('73', plain, ((v3_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('74', plain, ((v4_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('75', plain, ((v5_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('76', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('77', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((v2_struct_0 @ sk_A)
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | (r2_hidden @ X1 @ sk_D)
% 0.47/0.67          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.47/0.67  thf('78', plain,
% 0.47/0.67      ((~ (m1_subset_1 @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67           (u1_struct_0 @ sk_A))
% 0.47/0.67        | (r2_hidden @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67           sk_D)
% 0.47/0.67        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.67        | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['69', '77'])).
% 0.47/0.67  thf('79', plain,
% 0.47/0.67      ((m1_subset_1 @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.47/0.67  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('81', plain,
% 0.47/0.67      (((r2_hidden @ 
% 0.47/0.67         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67         sk_D)
% 0.47/0.67        | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.47/0.67  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('83', plain,
% 0.47/0.67      ((r2_hidden @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        sk_D)),
% 0.47/0.67      inference('clc', [status(thm)], ['81', '82'])).
% 0.47/0.67  thf('84', plain,
% 0.47/0.67      ((m1_subset_1 @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.47/0.67  thf('85', plain, (((sk_B) = (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(t80_orders_2, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.67         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.67           ( ![C:$i]:
% 0.47/0.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.67               ( ![D:$i]:
% 0.47/0.67                 ( ( m1_orders_1 @ D @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.67                   ( ![E:$i]:
% 0.47/0.67                     ( ( m2_orders_2 @ E @ A @ D ) =>
% 0.47/0.67                       ( ( ( r2_hidden @ B @ E ) & 
% 0.47/0.67                           ( ( C ) = ( k1_funct_1 @ D @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.67                         ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.67  thf('86', plain,
% 0.47/0.67      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.47/0.67          | ~ (m1_orders_1 @ X23 @ (k1_orders_1 @ (u1_struct_0 @ X22)))
% 0.47/0.67          | ((X24) != (k1_funct_1 @ X23 @ (u1_struct_0 @ X22)))
% 0.47/0.67          | (r3_orders_2 @ X22 @ X24 @ X21)
% 0.47/0.67          | ~ (r2_hidden @ X21 @ X25)
% 0.47/0.67          | ~ (m2_orders_2 @ X25 @ X22 @ X23)
% 0.47/0.67          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 0.47/0.67          | ~ (l1_orders_2 @ X22)
% 0.47/0.67          | ~ (v5_orders_2 @ X22)
% 0.47/0.67          | ~ (v4_orders_2 @ X22)
% 0.47/0.67          | ~ (v3_orders_2 @ X22)
% 0.47/0.67          | (v2_struct_0 @ X22))),
% 0.47/0.67      inference('cnf', [status(esa)], [t80_orders_2])).
% 0.47/0.67  thf('87', plain,
% 0.47/0.67      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.47/0.67         ((v2_struct_0 @ X22)
% 0.47/0.67          | ~ (v3_orders_2 @ X22)
% 0.47/0.67          | ~ (v4_orders_2 @ X22)
% 0.47/0.67          | ~ (v5_orders_2 @ X22)
% 0.47/0.67          | ~ (l1_orders_2 @ X22)
% 0.47/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ X23 @ (u1_struct_0 @ X22)) @ 
% 0.47/0.67               (u1_struct_0 @ X22))
% 0.47/0.67          | ~ (m2_orders_2 @ X25 @ X22 @ X23)
% 0.47/0.67          | ~ (r2_hidden @ X21 @ X25)
% 0.47/0.67          | (r3_orders_2 @ X22 @ (k1_funct_1 @ X23 @ (u1_struct_0 @ X22)) @ X21)
% 0.47/0.67          | ~ (m1_orders_1 @ X23 @ (k1_orders_1 @ (u1_struct_0 @ X22)))
% 0.47/0.67          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['86'])).
% 0.47/0.67  thf('88', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | ~ (m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.67          | (r3_orders_2 @ sk_A @ 
% 0.47/0.67             (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.47/0.67          | ~ (r2_hidden @ X0 @ X1)
% 0.47/0.67          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_C_1)
% 0.47/0.67          | ~ (l1_orders_2 @ sk_A)
% 0.47/0.67          | ~ (v5_orders_2 @ sk_A)
% 0.47/0.67          | ~ (v4_orders_2 @ sk_A)
% 0.47/0.67          | ~ (v3_orders_2 @ sk_A)
% 0.47/0.67          | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['85', '87'])).
% 0.47/0.67  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('90', plain,
% 0.47/0.67      ((m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('91', plain, (((sk_B) = (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('93', plain, ((v5_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('94', plain, ((v4_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('95', plain, ((v3_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('96', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.67          | ~ (r2_hidden @ X0 @ X1)
% 0.47/0.67          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_C_1)
% 0.47/0.67          | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)],
% 0.47/0.67                ['88', '89', '90', '91', '92', '93', '94', '95'])).
% 0.47/0.67  thf('97', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((v2_struct_0 @ sk_A)
% 0.47/0.67          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.47/0.67          | ~ (r2_hidden @ 
% 0.47/0.67               (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.47/0.67                (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67               X0)
% 0.47/0.67          | (r3_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['84', '96'])).
% 0.47/0.67  thf('98', plain,
% 0.47/0.67      (((r3_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.47/0.67        | ~ (m2_orders_2 @ sk_D @ sk_A @ sk_C_1)
% 0.47/0.67        | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['83', '97'])).
% 0.47/0.67  thf('99', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('100', plain,
% 0.47/0.67      (((r3_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.47/0.67        | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['98', '99'])).
% 0.47/0.67  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('102', plain,
% 0.47/0.67      ((r3_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('clc', [status(thm)], ['100', '101'])).
% 0.47/0.67  thf('103', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_r3_orders_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.67         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.47/0.67         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.67       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.47/0.67  thf('104', plain,
% 0.47/0.67      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.47/0.67          | ~ (l1_orders_2 @ X12)
% 0.47/0.67          | ~ (v3_orders_2 @ X12)
% 0.47/0.67          | (v2_struct_0 @ X12)
% 0.47/0.67          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.47/0.67          | (r1_orders_2 @ X12 @ X11 @ X13)
% 0.47/0.67          | ~ (r3_orders_2 @ X12 @ X11 @ X13))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.47/0.67  thf('105', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.67          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | (v2_struct_0 @ sk_A)
% 0.47/0.67          | ~ (v3_orders_2 @ sk_A)
% 0.47/0.67          | ~ (l1_orders_2 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['103', '104'])).
% 0.47/0.67  thf('106', plain, ((v3_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('108', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.67          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.67          | (v2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.47/0.67  thf('109', plain,
% 0.47/0.67      (((v2_struct_0 @ sk_A)
% 0.47/0.67        | ~ (m1_subset_1 @ 
% 0.47/0.67             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67             (u1_struct_0 @ sk_A))
% 0.47/0.67        | (r1_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['102', '108'])).
% 0.47/0.67  thf('110', plain,
% 0.47/0.67      ((m1_subset_1 @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.47/0.67        (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.47/0.67  thf('111', plain,
% 0.47/0.67      (((v2_struct_0 @ sk_A)
% 0.47/0.67        | (r1_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['109', '110'])).
% 0.47/0.67  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('113', plain,
% 0.47/0.67      ((r1_orders_2 @ sk_A @ sk_B @ 
% 0.47/0.67        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('clc', [status(thm)], ['111', '112'])).
% 0.47/0.67  thf('114', plain,
% 0.47/0.67      (((sk_B)
% 0.47/0.67         = (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['68', '113'])).
% 0.47/0.67  thf('115', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.47/0.67      inference('demod', [status(thm)], ['50', '114'])).
% 0.47/0.67  thf('116', plain, ($false), inference('demod', [status(thm)], ['5', '115'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
