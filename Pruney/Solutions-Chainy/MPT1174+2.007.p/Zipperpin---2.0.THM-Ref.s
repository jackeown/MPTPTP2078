%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HtdCOvVJzB

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 608 expanded)
%              Number of leaves         :   32 ( 193 expanded)
%              Depth                    :   22
%              Number of atoms          : 1308 (13032 expanded)
%              Number of equality atoms :   15 ( 596 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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

thf('1',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m2_orders_2 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

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

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 )
      | ~ ( v4_orders_2 @ X3 )
      | ~ ( v3_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X3 @ X2 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('24',plain,
    ( ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r1_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_orders_2 @ X12 @ X13 @ X11 )
      | ~ ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t30_orders_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('36',plain,
    ( ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k3_orders_2 @ sk_A @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

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

thf('40',plain,(
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

thf('41',plain,(
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
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r2_orders_2 @ sk_A @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','52'])).

thf('54',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('56',plain,(
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

thf('57',plain,(
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
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('70',plain,
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

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X21
       != ( k1_funct_1 @ X20 @ ( u1_struct_0 @ X19 ) ) )
      | ( r3_orders_2 @ X19 @ X21 @ X18 )
      | ~ ( r2_hidden @ X18 @ X22 )
      | ~ ( m2_orders_2 @ X22 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t80_orders_2])).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X20 @ ( u1_struct_0 @ X19 ) ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m2_orders_2 @ X22 @ X19 @ X20 )
      | ~ ( r2_hidden @ X18 @ X22 )
      | ( r3_orders_2 @ X19 @ ( k1_funct_1 @ X20 @ ( u1_struct_0 @ X19 ) ) @ X18 )
      | ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_orders_1 @ sk_C_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( sk_B
    = ( k1_funct_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','81'])).

thf('83',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m2_orders_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','82'])).

thf('84',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r3_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r1_orders_2 @ X9 @ X8 @ X10 )
      | ~ ( r3_orders_2 @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['53','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HtdCOvVJzB
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.60  % Solved by: fo/fo7.sh
% 0.20/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.60  % done 117 iterations in 0.137s
% 0.20/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.60  % SZS output start Refutation
% 0.20/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.60  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.60  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.20/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.60  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.60  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.60  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.60  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.60  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.60  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.20/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.60  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.60  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.60  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.60  thf(t81_orders_2, conjecture,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60           ( ![C:$i]:
% 0.20/0.60             ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60               ( ![D:$i]:
% 0.20/0.60                 ( ( m2_orders_2 @ D @ A @ C ) =>
% 0.20/0.60                   ( ( ( B ) = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60                     ( ( k3_orders_2 @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.60    (~( ![A:$i]:
% 0.20/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.60            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.60          ( ![B:$i]:
% 0.20/0.60            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60              ( ![C:$i]:
% 0.20/0.60                ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60                  ( ![D:$i]:
% 0.20/0.60                    ( ( m2_orders_2 @ D @ A @ C ) =>
% 0.20/0.60                      ( ( ( B ) = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60                        ( ( k3_orders_2 @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.60    inference('cnf.neg', [status(esa)], [t81_orders_2])).
% 0.20/0.60  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('1', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('2', plain,
% 0.20/0.60      ((m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(dt_m2_orders_2, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.60         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.60       ( ![C:$i]:
% 0.20/0.60         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.60           ( ( v6_orders_2 @ C @ A ) & 
% 0.20/0.60             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.60  thf('3', plain,
% 0.20/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.60         (~ (l1_orders_2 @ X5)
% 0.20/0.60          | ~ (v5_orders_2 @ X5)
% 0.20/0.60          | ~ (v4_orders_2 @ X5)
% 0.20/0.60          | ~ (v3_orders_2 @ X5)
% 0.20/0.60          | (v2_struct_0 @ X5)
% 0.20/0.60          | ~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X5)))
% 0.20/0.60          | (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.60          | ~ (m2_orders_2 @ X7 @ X5 @ X6))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.20/0.60  thf('4', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.20/0.60          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | (v2_struct_0 @ sk_A)
% 0.20/0.60          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.60          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.60  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('6', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('9', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.20/0.60          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.60  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('11', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1))),
% 0.20/0.60      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('12', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.60  thf(dt_k3_orders_2, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i]:
% 0.20/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60       ( m1_subset_1 @
% 0.20/0.60         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.60  thf('13', plain,
% 0.20/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.60          | ~ (l1_orders_2 @ X3)
% 0.20/0.60          | ~ (v5_orders_2 @ X3)
% 0.20/0.60          | ~ (v4_orders_2 @ X3)
% 0.20/0.60          | ~ (v3_orders_2 @ X3)
% 0.20/0.60          | (v2_struct_0 @ X3)
% 0.20/0.60          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.60          | (m1_subset_1 @ (k3_orders_2 @ X3 @ X2 @ X4) @ 
% 0.20/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.20/0.60  thf('14', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.20/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (v2_struct_0 @ sk_A)
% 0.20/0.60          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.60          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.60  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('16', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('17', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('19', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.20/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.60  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('21', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.20/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.60      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.60  thf('22', plain,
% 0.20/0.60      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.20/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['0', '21'])).
% 0.20/0.60  thf(t10_subset_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.60       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.60            ( ![C:$i]:
% 0.20/0.60              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.60  thf('23', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.20/0.60          | ((X0) = (k1_xboole_0))
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.20/0.60  thf('24', plain,
% 0.20/0.60      ((((k3_orders_2 @ sk_A @ sk_D @ sk_B) = (k1_xboole_0))
% 0.20/0.60        | (m1_subset_1 @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60           (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.60  thf('25', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('26', plain,
% 0.20/0.60      ((m1_subset_1 @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.60  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t30_orders_2, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60           ( ![C:$i]:
% 0.20/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60               ( ~( ( r1_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.20/0.60  thf('28', plain,
% 0.20/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.20/0.60          | ~ (r2_orders_2 @ X12 @ X13 @ X11)
% 0.20/0.60          | ~ (r1_orders_2 @ X12 @ X11 @ X13)
% 0.20/0.60          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.60          | ~ (l1_orders_2 @ X12)
% 0.20/0.60          | ~ (v5_orders_2 @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [t30_orders_2])).
% 0.20/0.60  thf('29', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (v5_orders_2 @ sk_A)
% 0.20/0.60          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.60          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.60  thf('30', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('32', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.60          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.20/0.60      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.60  thf('33', plain,
% 0.20/0.60      ((~ (r2_orders_2 @ sk_A @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60           sk_B)
% 0.20/0.60        | ~ (r1_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['26', '32'])).
% 0.20/0.60  thf('34', plain,
% 0.20/0.60      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.20/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['0', '21'])).
% 0.20/0.60  thf('35', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.20/0.60          | ((X0) = (k1_xboole_0))
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.20/0.60  thf('36', plain,
% 0.20/0.60      ((((k3_orders_2 @ sk_A @ sk_D @ sk_B) = (k1_xboole_0))
% 0.20/0.60        | (r2_hidden @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60           (k3_orders_2 @ sk_A @ sk_D @ sk_B)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.60  thf('37', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('38', plain,
% 0.20/0.60      ((r2_hidden @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.20/0.60      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.20/0.60  thf('39', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.60  thf(t57_orders_2, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60           ( ![C:$i]:
% 0.20/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60               ( ![D:$i]:
% 0.20/0.60                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.20/0.60                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.60  thf('40', plain,
% 0.20/0.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.60          | ~ (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 0.20/0.60          | (r2_orders_2 @ X15 @ X14 @ X17)
% 0.20/0.60          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.20/0.60          | ~ (l1_orders_2 @ X15)
% 0.20/0.60          | ~ (v5_orders_2 @ X15)
% 0.20/0.60          | ~ (v4_orders_2 @ X15)
% 0.20/0.60          | ~ (v3_orders_2 @ X15)
% 0.20/0.60          | (v2_struct_0 @ X15))),
% 0.20/0.60      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.20/0.60  thf('41', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         ((v2_struct_0 @ sk_A)
% 0.20/0.60          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.60          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.60          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.20/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.60  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('43', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('44', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('46', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         ((v2_struct_0 @ sk_A)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.60          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.20/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.20/0.60  thf('47', plain,
% 0.20/0.60      ((~ (m1_subset_1 @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60           (u1_struct_0 @ sk_A))
% 0.20/0.60        | (r2_orders_2 @ sk_A @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60           sk_B)
% 0.20/0.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.60        | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['38', '46'])).
% 0.20/0.60  thf('48', plain,
% 0.20/0.60      ((m1_subset_1 @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.60  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('50', plain,
% 0.20/0.60      (((r2_orders_2 @ sk_A @ 
% 0.20/0.60         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60         sk_B)
% 0.20/0.60        | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.60  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('52', plain,
% 0.20/0.60      ((r2_orders_2 @ sk_A @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        sk_B)),
% 0.20/0.60      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.60  thf('53', plain,
% 0.20/0.60      (~ (r1_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60          (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['33', '52'])).
% 0.20/0.60  thf('54', plain,
% 0.20/0.60      ((r2_hidden @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        (k3_orders_2 @ sk_A @ sk_D @ sk_B))),
% 0.20/0.60      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.20/0.60  thf('55', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.60  thf('56', plain,
% 0.20/0.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.60          | ~ (r2_hidden @ X14 @ (k3_orders_2 @ X15 @ X16 @ X17))
% 0.20/0.60          | (r2_hidden @ X14 @ X16)
% 0.20/0.60          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.20/0.60          | ~ (l1_orders_2 @ X15)
% 0.20/0.60          | ~ (v5_orders_2 @ X15)
% 0.20/0.60          | ~ (v4_orders_2 @ X15)
% 0.20/0.60          | ~ (v3_orders_2 @ X15)
% 0.20/0.60          | (v2_struct_0 @ X15))),
% 0.20/0.60      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.20/0.60  thf('57', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         ((v2_struct_0 @ sk_A)
% 0.20/0.60          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.60          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (r2_hidden @ X1 @ sk_D)
% 0.20/0.60          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.20/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.60  thf('58', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('59', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('60', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('62', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         ((v2_struct_0 @ sk_A)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (r2_hidden @ X1 @ sk_D)
% 0.20/0.60          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.20/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.20/0.60  thf('63', plain,
% 0.20/0.60      ((~ (m1_subset_1 @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60           (u1_struct_0 @ sk_A))
% 0.20/0.60        | (r2_hidden @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60           sk_D)
% 0.20/0.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.60        | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['54', '62'])).
% 0.20/0.60  thf('64', plain,
% 0.20/0.60      ((m1_subset_1 @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.60  thf('65', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('66', plain,
% 0.20/0.60      (((r2_hidden @ 
% 0.20/0.60         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60         sk_D)
% 0.20/0.60        | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.60  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('68', plain,
% 0.20/0.60      ((r2_hidden @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        sk_D)),
% 0.20/0.60      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.60  thf('69', plain,
% 0.20/0.60      ((m1_subset_1 @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.60  thf('70', plain, (((sk_B) = (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t80_orders_2, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60           ( ![C:$i]:
% 0.20/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60               ( ![D:$i]:
% 0.20/0.60                 ( ( m1_orders_1 @ D @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60                   ( ![E:$i]:
% 0.20/0.60                     ( ( m2_orders_2 @ E @ A @ D ) =>
% 0.20/0.60                       ( ( ( r2_hidden @ B @ E ) & 
% 0.20/0.60                           ( ( C ) = ( k1_funct_1 @ D @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.60                         ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.60  thf('71', plain,
% 0.20/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.20/0.60          | ~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X19)))
% 0.20/0.60          | ((X21) != (k1_funct_1 @ X20 @ (u1_struct_0 @ X19)))
% 0.20/0.60          | (r3_orders_2 @ X19 @ X21 @ X18)
% 0.20/0.60          | ~ (r2_hidden @ X18 @ X22)
% 0.20/0.60          | ~ (m2_orders_2 @ X22 @ X19 @ X20)
% 0.20/0.60          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.20/0.60          | ~ (l1_orders_2 @ X19)
% 0.20/0.60          | ~ (v5_orders_2 @ X19)
% 0.20/0.60          | ~ (v4_orders_2 @ X19)
% 0.20/0.60          | ~ (v3_orders_2 @ X19)
% 0.20/0.60          | (v2_struct_0 @ X19))),
% 0.20/0.60      inference('cnf', [status(esa)], [t80_orders_2])).
% 0.20/0.60  thf('72', plain,
% 0.20/0.60      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.20/0.60         ((v2_struct_0 @ X19)
% 0.20/0.60          | ~ (v3_orders_2 @ X19)
% 0.20/0.60          | ~ (v4_orders_2 @ X19)
% 0.20/0.60          | ~ (v5_orders_2 @ X19)
% 0.20/0.60          | ~ (l1_orders_2 @ X19)
% 0.20/0.60          | ~ (m1_subset_1 @ (k1_funct_1 @ X20 @ (u1_struct_0 @ X19)) @ 
% 0.20/0.60               (u1_struct_0 @ X19))
% 0.20/0.60          | ~ (m2_orders_2 @ X22 @ X19 @ X20)
% 0.20/0.60          | ~ (r2_hidden @ X18 @ X22)
% 0.20/0.60          | (r3_orders_2 @ X19 @ (k1_funct_1 @ X20 @ (u1_struct_0 @ X19)) @ X18)
% 0.20/0.60          | ~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X19)))
% 0.20/0.60          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19)))),
% 0.20/0.60      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.60  thf('73', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | ~ (m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | (r3_orders_2 @ sk_A @ 
% 0.20/0.60             (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.60          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_C_1)
% 0.20/0.60          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.60          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.60          | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['70', '72'])).
% 0.20/0.60  thf('74', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('75', plain,
% 0.20/0.60      ((m1_orders_1 @ sk_C_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('76', plain, (((sk_B) = (k1_funct_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('78', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('79', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('80', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('81', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.60          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_C_1)
% 0.20/0.60          | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('demod', [status(thm)],
% 0.20/0.60                ['73', '74', '75', '76', '77', '78', '79', '80'])).
% 0.20/0.60  thf('82', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((v2_struct_0 @ sk_A)
% 0.20/0.60          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.20/0.60          | ~ (r2_hidden @ 
% 0.20/0.60               (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ 
% 0.20/0.60                (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60               X0)
% 0.20/0.60          | (r3_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['69', '81'])).
% 0.20/0.60  thf('83', plain,
% 0.20/0.60      (((r3_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.20/0.60        | ~ (m2_orders_2 @ sk_D @ sk_A @ sk_C_1)
% 0.20/0.60        | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['68', '82'])).
% 0.20/0.60  thf('84', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('85', plain,
% 0.20/0.60      (((r3_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60         (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.20/0.60        | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('demod', [status(thm)], ['83', '84'])).
% 0.20/0.60  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('87', plain,
% 0.20/0.60      ((r3_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('clc', [status(thm)], ['85', '86'])).
% 0.20/0.60  thf('88', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(redefinition_r3_orders_2, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i]:
% 0.20/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.60         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.20/0.60  thf('89', plain,
% 0.20/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.60          | ~ (l1_orders_2 @ X9)
% 0.20/0.60          | ~ (v3_orders_2 @ X9)
% 0.20/0.60          | (v2_struct_0 @ X9)
% 0.20/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.60          | (r1_orders_2 @ X9 @ X8 @ X10)
% 0.20/0.60          | ~ (r3_orders_2 @ X9 @ X8 @ X10))),
% 0.20/0.60      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.20/0.60  thf('90', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.60          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (v2_struct_0 @ sk_A)
% 0.20/0.60          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.60          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.60  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('93', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.60          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | (v2_struct_0 @ sk_A))),
% 0.20/0.60      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.20/0.60  thf('94', plain,
% 0.20/0.60      (((v2_struct_0 @ sk_A)
% 0.20/0.60        | ~ (m1_subset_1 @ 
% 0.20/0.60             (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60             (u1_struct_0 @ sk_A))
% 0.20/0.60        | (r1_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['87', '93'])).
% 0.20/0.60  thf('95', plain,
% 0.20/0.60      ((m1_subset_1 @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60        (u1_struct_0 @ sk_A))),
% 0.20/0.60      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.60  thf('96', plain,
% 0.20/0.60      (((v2_struct_0 @ sk_A)
% 0.20/0.60        | (r1_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60           (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.60      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.60  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('98', plain,
% 0.20/0.60      ((r1_orders_2 @ sk_A @ sk_B @ 
% 0.20/0.60        (sk_C @ (k3_orders_2 @ sk_A @ sk_D @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('clc', [status(thm)], ['96', '97'])).
% 0.20/0.60  thf('99', plain, ($false), inference('demod', [status(thm)], ['53', '98'])).
% 0.20/0.60  
% 0.20/0.60  % SZS output end Refutation
% 0.20/0.60  
% 0.20/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
