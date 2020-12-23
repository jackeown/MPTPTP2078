%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2050+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.93SXOpvJv7

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:43 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  281 (4142 expanded)
%              Number of leaves         :   58 (1150 expanded)
%              Depth                    :   49
%              Number of atoms          : 4343 (65845 expanded)
%              Number of equality atoms :   76 ( 289 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_yellow19_type,type,(
    m1_yellow19: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_toler_1_type,type,(
    k1_toler_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k5_waybel_9_type,type,(
    k5_waybel_9: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t9_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_yellow19 @ C @ A @ B )
             => ( r1_waybel_0 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_yellow19 @ C @ A @ B )
               => ( r1_waybel_0 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_yellow19 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_yellow19 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow19 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_waybel_0 @ X33 @ X32 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_yellow19 @ X34 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow19])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d2_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_yellow19 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( C
                      = ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ D ) ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ ( k4_waybel_9 @ A @ B @ D ) ) ) )
                    & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( m1_yellow19 @ X9 @ X7 @ X6 )
      | ( m1_subset_1 @ ( sk_D_1 @ X9 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_yellow19])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_yellow19 @ sk_C @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_yellow19 @ sk_C @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(d11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ? [D: $i] :
                  ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( r1_orders_2 @ B @ D @ E )
                       => ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) )
                  & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ sk_B @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( r1_orders_2 @ X0 @ X2 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ sk_B @ X1 )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ sk_B @ X0 ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d7_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( l1_waybel_0 @ B @ A )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( ( l1_waybel_0 @ D @ A )
                    & ( v6_waybel_0 @ D @ A ) )
                 => ( ( D
                      = ( k4_waybel_9 @ A @ B @ C ) )
                  <=> ( ( ( u1_waybel_0 @ A @ D )
                        = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ( r2_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) @ ( k1_toler_1 @ ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ! [E: $i] :
                          ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) )
                        <=> ? [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                              & ( F = E )
                              & ( r1_orders_2 @ B @ C @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B )
    <=> ( ( r1_orders_2 @ B @ C @ F )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X14 ) )
      | ( X12 != X13 )
      | ~ ( r1_orders_2 @ X14 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('38',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r1_orders_2 @ X14 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X13 @ X11 @ X14 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_B @ X1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(redefinition_k5_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( k5_waybel_9 @ A @ B @ C )
        = ( k4_waybel_9 @ A @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( l1_waybel_0 @ X45 @ X46 )
      | ~ ( v7_waybel_0 @ X45 )
      | ~ ( v4_orders_2 @ X45 )
      | ( v2_struct_0 @ X45 )
      | ~ ( l1_struct_0 @ X46 )
      | ( v2_struct_0 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( u1_struct_0 @ X45 ) )
      | ( ( k5_waybel_9 @ X46 @ X45 @ X47 )
        = ( k4_waybel_9 @ X46 @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_waybel_9])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k5_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
        = ( k4_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k5_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
        = ( k4_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
      = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( ( v6_waybel_0 @ D @ A )
                    & ( l1_waybel_0 @ D @ A ) )
                 => ( ( D
                      = ( k4_waybel_9 @ A @ B @ C ) )
                  <=> ( ! [E: $i] :
                          ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) )
                        <=> ? [F: $i] :
                              ( zip_tseitin_0 @ F @ E @ C @ B ) )
                      & ( r2_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) @ ( k1_toler_1 @ ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ( ( u1_waybel_0 @ A @ D )
                        = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ~ ( v6_waybel_0 @ X17 @ X16 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( X17
       != ( k4_waybel_9 @ X16 @ X15 @ X18 ) )
      | ( r2_hidden @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X18 @ X15 )
      | ( r2_hidden @ X20 @ ( u1_struct_0 @ ( k4_waybel_9 @ X16 @ X15 @ X18 ) ) )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X16 @ X15 @ X18 ) @ X16 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X16 @ X15 @ X18 ) @ X16 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(dt_k5_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( v6_waybel_0 @ ( k5_waybel_9 @ A @ B @ C ) @ A )
        & ( m2_yellow_6 @ ( k5_waybel_9 @ A @ B @ C ) @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_waybel_0 @ X29 @ X30 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( v6_waybel_0 @ ( k5_waybel_9 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_9])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k5_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k5_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v6_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v6_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('77',plain,
    ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('78',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('80',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_waybel_0 @ X29 @ X30 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( m2_yellow_6 @ ( k5_waybel_9 @ X30 @ X29 @ X31 ) @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_9])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( m2_yellow_6 @ ( k5_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m2_yellow_6 @ ( k5_waybel_9 @ X0 @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m2_yellow_6 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m2_yellow_6 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m2_yellow_6 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m2_yellow_6 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['89','90'])).

thf(dt_m2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m2_yellow_6 @ C @ A @ B )
         => ( ~ ( v2_struct_0 @ C )
            & ( v4_orders_2 @ C )
            & ( v7_waybel_0 @ C )
            & ( l1_waybel_0 @ C @ A ) ) ) ) )).

thf('92',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v7_waybel_0 @ X36 )
      | ~ ( l1_waybel_0 @ X36 @ X35 )
      | ( l1_waybel_0 @ X37 @ X35 )
      | ~ ( m2_yellow_6 @ X37 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('93',plain,
    ( ( l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','74','75','76','77','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('107',plain,(
    ! [X53: $i,X54: $i] :
      ( ( m1_subset_1 @ X53 @ X54 )
      | ~ ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(t16_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) )
                     => ( ( D = E )
                       => ( ( k2_waybel_0 @ A @ B @ D )
                          = ( k2_waybel_0 @ A @ ( k4_waybel_9 @ A @ B @ C ) @ E ) ) ) ) ) ) ) ) )).

thf('110',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( v7_waybel_0 @ X48 )
      | ~ ( l1_waybel_0 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( u1_struct_0 @ X48 ) )
      | ( X50 != X51 )
      | ( ( k2_waybel_0 @ X49 @ X48 @ X50 )
        = ( k2_waybel_0 @ X49 @ ( k4_waybel_9 @ X49 @ X48 @ X52 ) @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ ( k4_waybel_9 @ X49 @ X48 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t16_waybel_9])).

thf('111',plain,(
    ! [X48: $i,X49: $i,X51: $i,X52: $i] :
      ( ( v2_struct_0 @ X49 )
      | ~ ( l1_struct_0 @ X49 )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ X48 ) )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ ( k4_waybel_9 @ X49 @ X48 @ X52 ) ) )
      | ( ( k2_waybel_0 @ X49 @ X48 @ X51 )
        = ( k2_waybel_0 @ X49 @ ( k4_waybel_9 @ X49 @ X48 @ X52 ) @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( u1_struct_0 @ X48 ) )
      | ~ ( l1_waybel_0 @ X48 @ X49 )
      | ~ ( v7_waybel_0 @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_waybel_0 @ sk_A @ sk_B @ X0 )
        = ( k2_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('116',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_waybel_0 @ sk_A @ sk_B @ X0 )
        = ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['100','101'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(d8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( k2_waybel_0 @ A @ B @ C )
                = ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) )).

thf('125',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( ( k2_waybel_0 @ X24 @ X23 @ X25 )
        = ( k3_funct_2 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) @ ( u1_waybel_0 @ X24 @ X23 ) @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d8_waybel_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('132',plain,(
    l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['100','101'])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('133',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('134',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('137',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ X42 )
      | ( ( k3_funct_2 @ X42 @ X43 @ X41 @ X44 )
        = ( k1_funct_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ X0 )
        = ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['100','101'])).

thf('140',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('141',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    l1_waybel_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['100','101'])).

thf('145',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ( v1_funct_2 @ ( u1_waybel_0 @ X38 @ X39 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('146',plain,
    ( ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ X0 )
        = ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['138','143','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['131','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['130','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('154',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('155',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( r2_hidden @ X57 @ X58 )
      | ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X60 @ X57 ) @ ( k2_relset_1 @ X58 @ X59 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_funct_2 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('158',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    m1_yellow19 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('162',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( m1_yellow19 @ X9 @ X7 @ X6 )
      | ( X9
        = ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X7 @ X6 @ ( sk_D_1 @ X9 @ X6 @ X7 ) ) ) @ ( u1_struct_0 @ X7 ) @ ( u1_waybel_0 @ X7 @ ( k4_waybel_9 @ X7 @ X6 @ ( sk_D_1 @ X9 @ X6 @ X7 ) ) ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_yellow19])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( sk_C
        = ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ) )
      | ~ ( m1_yellow19 @ sk_C @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_C
        = ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) ) ) )
      | ~ ( m1_yellow19 @ sk_C @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( sk_C
      = ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','165'])).

thf('167',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('169',plain,
    ( ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    = ( k4_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( sk_C
      = ( k2_relset_1 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C
      = ( k2_relset_1 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( sk_C
    = ( k2_relset_1 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ X0 ) @ sk_C )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['159','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( u1_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) @ sk_C )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['152','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['122','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) ) @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('185',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('189',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X61 @ X62 )
      | ~ ( v1_xboole_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    m2_yellow_6 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['89','90'])).

thf('194',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v7_waybel_0 @ X36 )
      | ~ ( l1_waybel_0 @ X36 @ X35 )
      | ~ ( v2_struct_0 @ X37 )
      | ~ ( m2_yellow_6 @ X37 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('195',plain,
    ( ~ ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ~ ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196','197','198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ~ ( v2_struct_0 @ ( k5_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['192','204'])).

thf('206',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['211','212'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('214',plain,(
    ! [X40: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('215',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('216',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('217',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('218',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['215','218','219'])).

thf('221',plain,(
    $false ),
    inference(demod,[status(thm)],['0','220'])).


%------------------------------------------------------------------------------
