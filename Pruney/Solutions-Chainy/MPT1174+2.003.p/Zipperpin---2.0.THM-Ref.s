%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rwhLMKCQaM

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:09 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 627 expanded)
%              Number of leaves         :   33 ( 198 expanded)
%              Depth                    :   25
%              Number of atoms          : 1452 (13456 expanded)
%              Number of equality atoms :   17 ( 614 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_orders_2 @ X6 @ X5 @ X7 )
      | ( X5 != X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( r2_orders_2 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m2_orders_2 @ X13 @ X11 @ X12 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X9 @ X8 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k3_orders_2 @ X22 @ X23 @ X24 ) )
      | ( r2_orders_2 @ X22 @ X21 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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

thf('53',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( r2_orders_2 @ X18 @ X17 @ X19 )
      | ~ ( r2_orders_2 @ X18 @ X20 @ X19 )
      | ~ ( r1_orders_2 @ X18 @ X17 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t32_orders_2])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k3_orders_2 @ X22 @ X23 @ X24 ) )
      | ( r2_hidden @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('63',plain,(
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
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('76',plain,
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

thf('77',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( X28
       != ( k1_funct_1 @ X27 @ ( u1_struct_0 @ X26 ) ) )
      | ( r3_orders_2 @ X26 @ X28 @ X25 )
      | ~ ( r2_hidden @ X25 @ X29 )
      | ~ ( m2_orders_2 @ X29 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t80_orders_2])).

thf('78',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X27 @ ( u1_struct_0 @ X26 ) ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m2_orders_2 @ X29 @ X26 @ X27 )
      | ~ ( r2_hidden @ X25 @ X29 )
      | ( r3_orders_2 @ X26 @ ( k1_funct_1 @ X27 @ ( u1_struct_0 @ X26 ) ) @ X25 )
      | ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
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
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_orders_1 @ sk_C_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( sk_B
    = ( k1_funct_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m2_orders_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','88'])).

thf('90',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r3_orders_2 @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','104'])).

thf('106',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['5','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rwhLMKCQaM
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:18:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 165 iterations in 0.169s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.44/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.61  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.61  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.44/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.61  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.44/0.61  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.61  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.44/0.61  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.44/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.61  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.44/0.61  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.44/0.61  thf(t81_orders_2, conjecture,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.61         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.61           ( ![C:$i]:
% 0.44/0.61             ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61               ( ![D:$i]:
% 0.44/0.61                 ( ( m2_orders_2 @ D @ A @ C ) =>
% 0.44/0.61                   ( ( ( B ) = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.61                     ( ( k3_orders_2 @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62              ( ![C:$i]:
% 0.44/0.62                ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                  ( ![D:$i]:
% 0.44/0.62                    ( ( m2_orders_2 @ D @ A @ C ) =>
% 0.44/0.62                      ( ( ( B ) = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                        ( ( k3_orders_2 @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t81_orders_2])).
% 0.44/0.62  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(d10_orders_2, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_orders_2 @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62           ( ![C:$i]:
% 0.44/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.44/0.62                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.44/0.62          | ~ (r2_orders_2 @ X6 @ X5 @ X7)
% 0.44/0.62          | ((X5) != (X7))
% 0.44/0.62          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.44/0.62          | ~ (l1_orders_2 @ X6))),
% 0.44/0.62      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X6 : $i, X7 : $i]:
% 0.44/0.62         (~ (l1_orders_2 @ X6)
% 0.44/0.62          | ~ (r2_orders_2 @ X6 @ X7 @ X7)
% 0.44/0.62          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_B) | ~ (l1_orders_2 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['0', '2'])).
% 0.44/0.62  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('5', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.44/0.62      inference('demod', [status(thm)], ['3', '4'])).
% 0.44/0.62  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('7', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      ((m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(dt_m2_orders_2, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.44/0.62         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62       ( ![C:$i]:
% 0.44/0.62         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.44/0.62           ( ( v6_orders_2 @ C @ A ) & 
% 0.44/0.62             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.62         (~ (l1_orders_2 @ X11)
% 0.44/0.62          | ~ (v5_orders_2 @ X11)
% 0.44/0.62          | ~ (v4_orders_2 @ X11)
% 0.44/0.62          | ~ (v3_orders_2 @ X11)
% 0.44/0.62          | (v2_struct_0 @ X11)
% 0.44/0.62          | ~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X11)))
% 0.44/0.62          | (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.44/0.62          | ~ (m2_orders_2 @ X13 @ X11 @ X12))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.44/0.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | (v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v3_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v4_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.62  thf('11', plain, ((v3_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('12', plain, ((v4_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.44/0.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.44/0.62  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1))),
% 0.44/0.62      inference('clc', [status(thm)], ['15', '16'])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '17'])).
% 0.44/0.62  thf(dt_k3_orders_2, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.44/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.44/0.62         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62       ( m1_subset_1 @
% 0.44/0.62         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.44/0.62          | ~ (l1_orders_2 @ X9)
% 0.44/0.62          | ~ (v5_orders_2 @ X9)
% 0.44/0.62          | ~ (v4_orders_2 @ X9)
% 0.44/0.62          | ~ (v3_orders_2 @ X9)
% 0.44/0.62          | (v2_struct_0 @ X9)
% 0.44/0.62          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.44/0.62          | (m1_subset_1 @ (k3_orders_2 @ X9 @ X8 @ X10) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v3_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v4_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.62  thf('21', plain, ((v3_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('22', plain, ((v4_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('23', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.44/0.62  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('clc', [status(thm)], ['25', '26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '27'])).
% 0.44/0.62  thf(t10_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.44/0.62            ( ![C:$i]:
% 0.44/0.62              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.44/0.62          | ((X0) = (k1_xboole_0))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      ((((k3_orders_2 @ sk_A @ sk_D @ sk_B) = (k1_xboole_0))
% 0.44/0.62        | (r2_hidden @ 
% 0.44/0.62           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.44/0.62  thf('31', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      ((r2_hidden @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '17'])).
% 0.44/0.62  thf(t57_orders_2, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62           ( ![C:$i]:
% 0.44/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62               ( ![D:$i]:
% 0.44/0.62                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.44/0.62                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.44/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.44/0.62          | ~ (r2_hidden @ X21 @ (k3_orders_2 @ X22 @ X23 @ X24))
% 0.44/0.62          | (r2_orders_2 @ X22 @ X21 @ X24)
% 0.44/0.62          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 0.44/0.62          | ~ (l1_orders_2 @ X22)
% 0.44/0.62          | ~ (v5_orders_2 @ X22)
% 0.44/0.62          | ~ (v4_orders_2 @ X22)
% 0.44/0.62          | ~ (v3_orders_2 @ X22)
% 0.44/0.62          | (v2_struct_0 @ X22))),
% 0.44/0.62      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v3_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v4_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.62  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      ((~ (m1_subset_1 @ 
% 0.44/0.62           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           (u1_struct_0 @ sk_A))
% 0.44/0.62        | (r2_orders_2 @ sk_A @ 
% 0.44/0.62           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           sk_B)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['32', '40'])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '27'])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.44/0.62          | ((X0) = (k1_xboole_0))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      ((((k3_orders_2 @ sk_A @ sk_D @ sk_B) = (k1_xboole_0))
% 0.44/0.62        | (m1_subset_1 @ 
% 0.44/0.62           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.62  thf('45', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      ((m1_subset_1 @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.44/0.62  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      (((r2_orders_2 @ sk_A @ 
% 0.44/0.62         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62         sk_B)
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['41', '46', '47'])).
% 0.44/0.62  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      ((r2_orders_2 @ sk_A @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        sk_B)),
% 0.44/0.62      inference('clc', [status(thm)], ['48', '49'])).
% 0.44/0.62  thf('51', plain,
% 0.44/0.62      ((m1_subset_1 @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.44/0.62  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t32_orders_2, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62           ( ![C:$i]:
% 0.44/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62               ( ![D:$i]:
% 0.44/0.62                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62                   ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.44/0.62                         ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.44/0.62                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.44/0.62                         ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.44/0.62                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('53', plain,
% 0.44/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.44/0.62          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.44/0.62          | (r2_orders_2 @ X18 @ X17 @ X19)
% 0.44/0.62          | ~ (r2_orders_2 @ X18 @ X20 @ X19)
% 0.44/0.62          | ~ (r1_orders_2 @ X18 @ X17 @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.44/0.62          | ~ (l1_orders_2 @ X18)
% 0.44/0.62          | ~ (v5_orders_2 @ X18)
% 0.44/0.62          | ~ (v4_orders_2 @ X18))),
% 0.44/0.62      inference('cnf', [status(esa)], [t32_orders_2])).
% 0.44/0.62  thf('54', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (v4_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | (r2_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.44/0.62  thf('55', plain, ((v4_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('56', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('58', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | (r2_orders_2 @ sk_A @ sk_B @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.44/0.62  thf('59', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (r2_orders_2 @ sk_A @ 
% 0.44/0.62               (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.44/0.62                (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62               X0)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ sk_B @ 
% 0.44/0.62               (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.44/0.62                (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['51', '58'])).
% 0.44/0.62  thf('60', plain,
% 0.44/0.62      ((r2_hidden @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.44/0.62  thf('61', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '17'])).
% 0.44/0.62  thf('62', plain,
% 0.44/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.44/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.44/0.62          | ~ (r2_hidden @ X21 @ (k3_orders_2 @ X22 @ X23 @ X24))
% 0.44/0.62          | (r2_hidden @ X21 @ X23)
% 0.44/0.62          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 0.44/0.62          | ~ (l1_orders_2 @ X22)
% 0.44/0.62          | ~ (v5_orders_2 @ X22)
% 0.44/0.62          | ~ (v4_orders_2 @ X22)
% 0.44/0.62          | ~ (v3_orders_2 @ X22)
% 0.44/0.62          | (v2_struct_0 @ X22))),
% 0.44/0.62      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.44/0.62  thf('63', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v3_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v4_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (r2_hidden @ X1 @ sk_D)
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.44/0.62  thf('64', plain, ((v3_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('65', plain, ((v4_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('66', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('68', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (r2_hidden @ X1 @ sk_D)
% 0.44/0.62          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.44/0.62  thf('69', plain,
% 0.44/0.62      ((~ (m1_subset_1 @ 
% 0.44/0.62           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           (u1_struct_0 @ sk_A))
% 0.44/0.62        | (r2_hidden @ 
% 0.44/0.62           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           sk_D)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['60', '68'])).
% 0.44/0.62  thf('70', plain,
% 0.44/0.62      ((m1_subset_1 @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.44/0.62  thf('71', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('72', plain,
% 0.44/0.62      (((r2_hidden @ 
% 0.44/0.62         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62         sk_D)
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.44/0.62  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('74', plain,
% 0.44/0.62      ((r2_hidden @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        sk_D)),
% 0.44/0.62      inference('clc', [status(thm)], ['72', '73'])).
% 0.44/0.62  thf('75', plain,
% 0.44/0.62      ((m1_subset_1 @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.44/0.62  thf('76', plain, (((sk_B) = (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t80_orders_2, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62           ( ![C:$i]:
% 0.44/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62               ( ![D:$i]:
% 0.44/0.62                 ( ( m1_orders_1 @ D @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                   ( ![E:$i]:
% 0.44/0.62                     ( ( m2_orders_2 @ E @ A @ D ) =>
% 0.44/0.62                       ( ( ( r2_hidden @ B @ E ) & 
% 0.44/0.62                           ( ( C ) = ( k1_funct_1 @ D @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62                         ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('77', plain,
% 0.44/0.62      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.44/0.62          | ~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X26)))
% 0.44/0.62          | ((X28) != (k1_funct_1 @ X27 @ (u1_struct_0 @ X26)))
% 0.44/0.62          | (r3_orders_2 @ X26 @ X28 @ X25)
% 0.44/0.62          | ~ (r2_hidden @ X25 @ X29)
% 0.44/0.62          | ~ (m2_orders_2 @ X29 @ X26 @ X27)
% 0.44/0.62          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.44/0.62          | ~ (l1_orders_2 @ X26)
% 0.44/0.62          | ~ (v5_orders_2 @ X26)
% 0.44/0.62          | ~ (v4_orders_2 @ X26)
% 0.44/0.62          | ~ (v3_orders_2 @ X26)
% 0.44/0.62          | (v2_struct_0 @ X26))),
% 0.44/0.62      inference('cnf', [status(esa)], [t80_orders_2])).
% 0.44/0.62  thf('78', plain,
% 0.44/0.62      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 0.44/0.62         ((v2_struct_0 @ X26)
% 0.44/0.62          | ~ (v3_orders_2 @ X26)
% 0.44/0.62          | ~ (v4_orders_2 @ X26)
% 0.44/0.62          | ~ (v5_orders_2 @ X26)
% 0.44/0.62          | ~ (l1_orders_2 @ X26)
% 0.44/0.62          | ~ (m1_subset_1 @ (k1_funct_1 @ X27 @ (u1_struct_0 @ X26)) @ 
% 0.44/0.62               (u1_struct_0 @ X26))
% 0.44/0.62          | ~ (m2_orders_2 @ X29 @ X26 @ X27)
% 0.44/0.62          | ~ (r2_hidden @ X25 @ X29)
% 0.44/0.62          | (r3_orders_2 @ X26 @ (k1_funct_1 @ X27 @ (u1_struct_0 @ X26)) @ X25)
% 0.44/0.62          | ~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X26)))
% 0.44/0.62          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['77'])).
% 0.44/0.62  thf('79', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | (r3_orders_2 @ sk_A @ 
% 0.44/0.62             (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.44/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.44/0.62          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_C_1)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v4_orders_2 @ sk_A)
% 0.44/0.62          | ~ (v3_orders_2 @ sk_A)
% 0.44/0.62          | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['76', '78'])).
% 0.44/0.62  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('81', plain,
% 0.44/0.62      ((m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('82', plain, (((sk_B) = (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('83', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('85', plain, ((v4_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('86', plain, ((v3_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('87', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.44/0.62          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_C_1)
% 0.44/0.62          | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)],
% 0.44/0.62                ['79', '80', '81', '82', '83', '84', '85', '86'])).
% 0.44/0.62  thf('88', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.44/0.62          | ~ (r2_hidden @ 
% 0.44/0.62               (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.44/0.62                (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62               X0)
% 0.44/0.62          | (r3_orders_2 @ sk_A @ sk_B @ 
% 0.44/0.62             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['75', '87'])).
% 0.44/0.62  thf('89', plain,
% 0.44/0.62      (((r3_orders_2 @ sk_A @ sk_B @ 
% 0.44/0.62         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ~ (m2_orders_2 @ sk_D @ sk_A @ sk_C_1)
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['74', '88'])).
% 0.44/0.62  thf('90', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('91', plain,
% 0.44/0.62      (((r3_orders_2 @ sk_A @ sk_B @ 
% 0.44/0.62         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['89', '90'])).
% 0.44/0.62  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('93', plain,
% 0.44/0.62      ((r3_orders_2 @ sk_A @ sk_B @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('clc', [status(thm)], ['91', '92'])).
% 0.44/0.62  thf('94', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_r3_orders_2, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.44/0.62         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.44/0.62  thf('95', plain,
% 0.44/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.44/0.62          | ~ (l1_orders_2 @ X15)
% 0.44/0.62          | ~ (v3_orders_2 @ X15)
% 0.44/0.62          | (v2_struct_0 @ X15)
% 0.44/0.62          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.44/0.62          | (r1_orders_2 @ X15 @ X14 @ X16)
% 0.44/0.62          | ~ (r3_orders_2 @ X15 @ X14 @ X16))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.44/0.62  thf('96', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (v2_struct_0 @ sk_A)
% 0.44/0.62          | ~ (v3_orders_2 @ sk_A)
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.62  thf('97', plain, ((v3_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('98', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('99', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.44/0.62  thf('100', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (m1_subset_1 @ 
% 0.44/0.62             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62             (u1_struct_0 @ sk_A))
% 0.44/0.62        | (r1_orders_2 @ sk_A @ sk_B @ 
% 0.44/0.62           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['93', '99'])).
% 0.44/0.62  thf('101', plain,
% 0.44/0.62      ((m1_subset_1 @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62        (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.44/0.62  thf('102', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | (r1_orders_2 @ sk_A @ sk_B @ 
% 0.44/0.62           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('demod', [status(thm)], ['100', '101'])).
% 0.44/0.62  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('104', plain,
% 0.44/0.62      ((r1_orders_2 @ sk_A @ sk_B @ 
% 0.44/0.62        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('clc', [status(thm)], ['102', '103'])).
% 0.44/0.62  thf('105', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.44/0.62          | ~ (r2_orders_2 @ sk_A @ 
% 0.44/0.62               (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.44/0.62                (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62               X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['59', '104'])).
% 0.44/0.62  thf('106', plain,
% 0.44/0.62      (((r2_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['50', '105'])).
% 0.44/0.62  thf('107', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('108', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.44/0.62      inference('demod', [status(thm)], ['106', '107'])).
% 0.44/0.62  thf('109', plain, ($false), inference('demod', [status(thm)], ['5', '108'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
