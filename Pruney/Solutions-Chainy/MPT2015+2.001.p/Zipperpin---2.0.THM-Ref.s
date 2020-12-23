%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TiQwtky0ir

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  182 (1328 expanded)
%              Number of leaves         :   48 ( 390 expanded)
%              Depth                    :   27
%              Number of atoms          : 1973 (21736 expanded)
%              Number of equality atoms :   39 ( 119 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_yellow_6_type,type,(
    v2_yellow_6: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_toler_1_type,type,(
    k1_toler_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t14_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( v2_yellow_6 @ ( k4_waybel_9 @ A @ B @ C ) @ A @ B )
                & ( m1_yellow_6 @ ( k4_waybel_9 @ A @ B @ C ) @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( ( v2_yellow_6 @ ( k4_waybel_9 @ A @ B @ C ) @ A @ B )
                  & ( m1_yellow_6 @ ( k4_waybel_9 @ A @ B @ C ) @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_waybel_9])).

thf('0',plain,
    ( ~ ( v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B )
    | ~ ( m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B )
   <= ~ ( v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A )
        & ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( l1_waybel_0 @ X41 @ X42 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_struct_0 @ X42 )
      | ( v2_struct_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X41 ) )
      | ( v6_waybel_0 @ ( k4_waybel_9 @ X42 @ X41 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B )
    <=> ( ( r1_orders_2 @ B @ C @ F )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ) )).

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

thf('14',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_waybel_0 @ X33 @ X34 )
      | ~ ( v6_waybel_0 @ X35 @ X34 )
      | ~ ( l1_waybel_0 @ X35 @ X34 )
      | ( X35
       != ( k4_waybel_9 @ X34 @ X33 @ X36 ) )
      | ( ( u1_waybel_0 @ X34 @ X35 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X34 ) @ ( u1_waybel_0 @ X34 @ X33 ) @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X33: $i,X34: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( l1_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X33 ) )
      | ( ( u1_waybel_0 @ X34 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X34 ) @ ( u1_waybel_0 @ X34 @ X33 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) @ X34 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) @ X34 )
      | ~ ( l1_waybel_0 @ X33 @ X34 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) @ X0 )
      | ( ( u1_waybel_0 @ X0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ ( u1_waybel_0 @ X0 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( l1_waybel_0 @ X41 @ X42 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_struct_0 @ X42 )
      | ( v2_struct_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X41 ) )
      | ( l1_waybel_0 @ ( k4_waybel_9 @ X42 @ X41 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(d8_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( l1_waybel_0 @ C @ A )
             => ( ( m1_yellow_6 @ C @ A @ B )
              <=> ( ( m1_yellow_0 @ C @ B )
                  & ( ( u1_waybel_0 @ A @ C )
                    = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_waybel_0 @ X22 @ X23 )
      | ~ ( m1_yellow_0 @ X24 @ X22 )
      | ( ( u1_waybel_0 @ X23 @ X24 )
       != ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) @ ( u1_waybel_0 @ X23 @ X22 ) @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_yellow_6 @ X24 @ X23 @ X22 )
      | ~ ( l1_waybel_0 @ X24 @ X23 )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('37',plain,
    ( ( ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
     != ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B )
    | ~ ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('40',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
     != ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) )
    | ( m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B )
    | ~ ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ~ ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( l1_waybel_0 @ X44 @ X45 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ X45 @ X44 @ X46 ) ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t13_waybel_9])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_tarski @ ( u1_orders_2 @ X12 ) @ ( u1_orders_2 @ X13 ) )
      | ( m1_yellow_0 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('55',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ~ ( r1_tarski @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ sk_B ) )
    | ~ ( l1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( l1_orders_2 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('58',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( l1_orders_2 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('63',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ~ ( r1_tarski @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','60','65'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('68',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('72',plain,(
    v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_waybel_0 @ X33 @ X34 )
      | ~ ( v6_waybel_0 @ X35 @ X34 )
      | ~ ( l1_waybel_0 @ X35 @ X34 )
      | ( X35
       != ( k4_waybel_9 @ X34 @ X33 @ X36 ) )
      | ( r2_relset_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X35 ) @ ( u1_orders_2 @ X35 ) @ ( k1_toler_1 @ ( u1_orders_2 @ X33 ) @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('75',plain,(
    ! [X33: $i,X34: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( l1_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X33 ) )
      | ( r2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) ) @ ( u1_orders_2 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) ) @ ( k1_toler_1 @ ( u1_orders_2 @ X33 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) @ X34 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X34 @ X33 @ X36 ) @ X34 )
      | ~ ( l1_waybel_0 @ X33 @ X34 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) @ X0 )
      | ( r2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) ) @ ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('80',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    r2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf(dt_k1_toler_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( m1_subset_1 @ ( k1_toler_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( m1_subset_1 @ ( k1_toler_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_toler_1])).

thf('87',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('88',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X7 = X10 )
      | ~ ( r2_relset_1 @ X8 @ X9 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( u1_orders_2 @ X0 )
        = ( k1_toler_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) @ ( k1_toler_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( l1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    l1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('93',plain,
    ( ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['71','93'])).

thf('95',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('96',plain,
    ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
    = ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf(redefinition_k1_toler_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k1_toler_1 @ A @ B )
        = ( k2_wellord1 @ A @ B ) ) ) )).

thf('97',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k1_toler_1 @ X18 @ X19 )
        = ( k2_wellord1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_toler_1])).

thf('98',plain,
    ( ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_wellord1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_wellord1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['70','98'])).

thf('100',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('101',plain,
    ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_wellord1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('102',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_wellord1 @ X2 @ X3 )
        = ( k3_xboole_0 @ X2 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r1_tarski @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','105'])).

thf('107',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('108',plain,(
    r1_tarski @ ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['66','108'])).

thf('110',plain,(
    m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['42','109'])).

thf('111',plain,
    ( ~ ( m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B )
   <= ~ ( m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B )
    | ~ ( m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,(
    ~ ( v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','114'])).

thf('116',plain,(
    m1_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['42','109'])).

thf(d9_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_yellow_6 @ C @ A @ B )
             => ( ( v2_yellow_6 @ C @ A @ B )
              <=> ( ( v4_yellow_0 @ C @ B )
                  & ( m1_yellow_0 @ C @ B ) ) ) ) ) ) )).

thf('117',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_waybel_0 @ X25 @ X26 )
      | ~ ( v4_yellow_0 @ X27 @ X25 )
      | ~ ( m1_yellow_0 @ X27 @ X25 )
      | ( v2_yellow_6 @ X27 @ X26 @ X25 )
      | ~ ( m1_yellow_6 @ X27 @ X26 @ X25 )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_6])).

thf('118',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B )
    | ~ ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ~ ( v4_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['66','108'])).

thf('121',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B )
    | ~ ( v4_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,
    ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
    = ( k1_toler_1 @ ( u1_orders_2 @ sk_B ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf(d14_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( v4_yellow_0 @ B @ A )
          <=> ( ( u1_orders_2 @ B )
              = ( k1_toler_1 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('124',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_yellow_0 @ X14 @ X15 )
      | ( ( u1_orders_2 @ X14 )
       != ( k1_toler_1 @ ( u1_orders_2 @ X15 ) @ ( u1_struct_0 @ X14 ) ) )
      | ( v4_yellow_0 @ X14 @ X15 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d14_yellow_0])).

thf('125',plain,
    ( ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
     != ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_B )
    | ( v4_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('127',plain,
    ( ( ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) )
     != ( u1_orders_2 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v4_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v4_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    m1_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['66','108'])).

thf('130',plain,(
    v4_yellow_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    v2_yellow_6 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['122','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['115','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TiQwtky0ir
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:27:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 112 iterations in 0.083s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.55  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.22/0.55  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.55  thf(k4_waybel_9_type, type, k4_waybel_9: $i > $i > $i > $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(v2_yellow_6_type, type, v2_yellow_6: $i > $i > $i > $o).
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(v4_yellow_0_type, type, v4_yellow_0: $i > $i > $o).
% 0.22/0.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.22/0.55  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.55  thf(k1_toler_1_type, type, k1_toler_1: $i > $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(t14_waybel_9, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.55               ( ( v2_yellow_6 @ ( k4_waybel_9 @ A @ B @ C ) @ A @ B ) & 
% 0.22/0.55                 ( m1_yellow_6 @ ( k4_waybel_9 @ A @ B @ C ) @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.55              ( ![C:$i]:
% 0.22/0.55                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.55                  ( ( v2_yellow_6 @ ( k4_waybel_9 @ A @ B @ C ) @ A @ B ) & 
% 0.22/0.55                    ( m1_yellow_6 @ ( k4_waybel_9 @ A @ B @ C ) @ A @ B ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t14_waybel_9])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((~ (v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)
% 0.22/0.55        | ~ (m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((~ (v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B))
% 0.22/0.55         <= (~
% 0.22/0.55             ((v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('2', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('3', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_k4_waybel_9, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.22/0.55         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.22/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.55       ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) & 
% 0.22/0.55         ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ))).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.55         (~ (l1_waybel_0 @ X41 @ X42)
% 0.22/0.55          | (v2_struct_0 @ X41)
% 0.22/0.55          | ~ (l1_struct_0 @ X42)
% 0.22/0.55          | (v2_struct_0 @ X42)
% 0.22/0.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X41))
% 0.22/0.55          | (v6_waybel_0 @ (k4_waybel_9 @ X42 @ X41 @ X43) @ X42))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v6_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C) @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_struct_0 @ X0)
% 0.22/0.55          | (v2_struct_0 @ sk_B)
% 0.22/0.55          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A)
% 0.22/0.55        | (v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.55  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | (v2_struct_0 @ sk_A)
% 0.22/0.55        | (v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('12', plain, ((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d7_waybel_9, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( l1_struct_0 @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( l1_waybel_0 @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( ( l1_waybel_0 @ D @ A ) & ( v6_waybel_0 @ D @ A ) ) =>
% 0.22/0.55                   ( ( ( D ) = ( k4_waybel_9 @ A @ B @ C ) ) <=>
% 0.22/0.55                     ( ( ( u1_waybel_0 @ A @ D ) =
% 0.22/0.55                         ( k2_partfun1 @
% 0.22/0.55                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.22/0.55                       ( r2_relset_1 @
% 0.22/0.55                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.22/0.55                         ( u1_orders_2 @ D ) @ 
% 0.22/0.55                         ( k1_toler_1 @
% 0.22/0.55                           ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.22/0.55                       ( ![E:$i]:
% 0.22/0.55                         ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) ) <=>
% 0.22/0.55                           ( ?[F:$i]:
% 0.22/0.55                             ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                               ( ( F ) = ( E ) ) & ( r1_orders_2 @ B @ C @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.55  thf(zf_stmt_2, axiom,
% 0.22/0.55    (![F:$i,E:$i,C:$i,B:$i]:
% 0.22/0.55     ( ( zip_tseitin_0 @ F @ E @ C @ B ) <=>
% 0.22/0.55       ( ( r1_orders_2 @ B @ C @ F ) & ( ( F ) = ( E ) ) & 
% 0.22/0.55         ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_3, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( ( v6_waybel_0 @ D @ A ) & ( l1_waybel_0 @ D @ A ) ) =>
% 0.22/0.55                   ( ( ( D ) = ( k4_waybel_9 @ A @ B @ C ) ) <=>
% 0.22/0.55                     ( ( ![E:$i]:
% 0.22/0.55                         ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) ) <=>
% 0.22/0.55                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B ) ) ) ) & 
% 0.22/0.55                       ( r2_relset_1 @
% 0.22/0.55                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.22/0.55                         ( u1_orders_2 @ D ) @ 
% 0.22/0.55                         ( k1_toler_1 @
% 0.22/0.55                           ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.22/0.55                       ( ( u1_waybel_0 @ A @ D ) =
% 0.22/0.55                         ( k2_partfun1 @
% 0.22/0.55                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X33)
% 0.22/0.55          | ~ (l1_waybel_0 @ X33 @ X34)
% 0.22/0.55          | ~ (v6_waybel_0 @ X35 @ X34)
% 0.22/0.55          | ~ (l1_waybel_0 @ X35 @ X34)
% 0.22/0.55          | ((X35) != (k4_waybel_9 @ X34 @ X33 @ X36))
% 0.22/0.55          | ((u1_waybel_0 @ X34 @ X35)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X34) @ 
% 0.22/0.55                 (u1_waybel_0 @ X34 @ X33) @ (u1_struct_0 @ X35)))
% 0.22/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X33))
% 0.22/0.55          | ~ (l1_struct_0 @ X34)
% 0.22/0.55          | (v2_struct_0 @ X34))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X33 : $i, X34 : $i, X36 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X34)
% 0.22/0.55          | ~ (l1_struct_0 @ X34)
% 0.22/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X33))
% 0.22/0.55          | ((u1_waybel_0 @ X34 @ (k4_waybel_9 @ X34 @ X33 @ X36))
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X34) @ 
% 0.22/0.55                 (u1_waybel_0 @ X34 @ X33) @ 
% 0.22/0.55                 (u1_struct_0 @ (k4_waybel_9 @ X34 @ X33 @ X36))))
% 0.22/0.55          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X34 @ X33 @ X36) @ X34)
% 0.22/0.55          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X34 @ X33 @ X36) @ X34)
% 0.22/0.55          | ~ (l1_waybel_0 @ X33 @ X34)
% 0.22/0.55          | (v2_struct_0 @ X33))),
% 0.22/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_B)
% 0.22/0.55          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.22/0.55          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C) @ X0)
% 0.22/0.55          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C) @ X0)
% 0.22/0.55          | ((u1_waybel_0 @ X0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C))
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.22/0.55                 (u1_waybel_0 @ X0 @ sk_B) @ 
% 0.22/0.55                 (u1_struct_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C))))
% 0.22/0.55          | ~ (l1_struct_0 @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '15'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | ((u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55               (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.22/0.55               (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))
% 0.22/0.55        | ~ (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.22/0.55        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '16'])).
% 0.22/0.55  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('19', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('20', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.55         (~ (l1_waybel_0 @ X41 @ X42)
% 0.22/0.55          | (v2_struct_0 @ X41)
% 0.22/0.55          | ~ (l1_struct_0 @ X42)
% 0.22/0.55          | (v2_struct_0 @ X42)
% 0.22/0.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X41))
% 0.22/0.55          | (l1_waybel_0 @ (k4_waybel_9 @ X42 @ X41 @ X43) @ X42))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((l1_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C) @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_struct_0 @ X0)
% 0.22/0.55          | (v2_struct_0 @ sk_B)
% 0.22/0.55          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A)
% 0.22/0.55        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['19', '22'])).
% 0.22/0.55  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | (v2_struct_0 @ sk_A)
% 0.22/0.55        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf('26', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('29', plain, ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('30', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55               (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.22/0.55               (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))
% 0.22/0.55        | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['17', '18', '29', '30'])).
% 0.22/0.55  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | ((u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55               (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.22/0.55               (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))))),
% 0.22/0.55      inference('clc', [status(thm)], ['31', '32'])).
% 0.22/0.55  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (((u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55            (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.55  thf(d8_yellow_6, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_struct_0 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( l1_waybel_0 @ B @ A ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( l1_waybel_0 @ C @ A ) =>
% 0.22/0.55               ( ( m1_yellow_6 @ C @ A @ B ) <=>
% 0.22/0.55                 ( ( m1_yellow_0 @ C @ B ) & 
% 0.22/0.55                   ( ( u1_waybel_0 @ A @ C ) =
% 0.22/0.55                     ( k2_partfun1 @
% 0.22/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                       ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.55         (~ (l1_waybel_0 @ X22 @ X23)
% 0.22/0.55          | ~ (m1_yellow_0 @ X24 @ X22)
% 0.22/0.55          | ((u1_waybel_0 @ X23 @ X24)
% 0.22/0.55              != (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23) @ 
% 0.22/0.55                  (u1_waybel_0 @ X23 @ X22) @ (u1_struct_0 @ X24)))
% 0.22/0.55          | (m1_yellow_6 @ X24 @ X23 @ X22)
% 0.22/0.55          | ~ (l1_waybel_0 @ X24 @ X23)
% 0.22/0.55          | ~ (l1_struct_0 @ X23))),
% 0.22/0.55      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      ((((u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55          != (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.22/0.55        | (m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)
% 0.22/0.55        | ~ (m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.55  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('39', plain, ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('40', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      ((((u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55          != (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.55        | (m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)
% 0.22/0.55        | ~ (m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      ((~ (m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | (m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B))),
% 0.22/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.55  thf('43', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('44', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t13_waybel_9, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.55               ( r1_tarski @
% 0.22/0.55                 ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.22/0.55                 ( u1_struct_0 @ B ) ) ) ) ) ) ))).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X44)
% 0.22/0.55          | ~ (l1_waybel_0 @ X44 @ X45)
% 0.22/0.55          | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ X45 @ X44 @ X46)) @ 
% 0.22/0.55             (u1_struct_0 @ X44))
% 0.22/0.55          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X44))
% 0.22/0.55          | ~ (l1_struct_0 @ X45)
% 0.22/0.55          | (v2_struct_0 @ X45))),
% 0.22/0.55      inference('cnf', [status(esa)], [t13_waybel_9])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_struct_0 @ X0)
% 0.22/0.55          | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C)) @ 
% 0.22/0.55             (u1_struct_0 @ sk_B))
% 0.22/0.55          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.22/0.55          | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_struct_0 @ sk_B))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['43', '46'])).
% 0.22/0.55  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_struct_0 @ sk_B))
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.55  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55        (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('clc', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf(d13_yellow_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_orders_2 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( l1_orders_2 @ B ) =>
% 0.22/0.55           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.22/0.55             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.55               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i]:
% 0.22/0.55         (~ (l1_orders_2 @ X12)
% 0.22/0.55          | ~ (r1_tarski @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13))
% 0.22/0.55          | ~ (r1_tarski @ (u1_orders_2 @ X12) @ (u1_orders_2 @ X13))
% 0.22/0.55          | (m1_yellow_0 @ X12 @ X13)
% 0.22/0.55          | ~ (l1_orders_2 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      ((~ (l1_orders_2 @ sk_B)
% 0.22/0.55        | (m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | ~ (r1_tarski @ (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55             (u1_orders_2 @ sk_B))
% 0.22/0.55        | ~ (l1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.55  thf('56', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_l1_waybel_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_struct_0 @ A ) =>
% 0.22/0.55       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      (![X20 : $i, X21 : $i]:
% 0.22/0.55         (~ (l1_waybel_0 @ X20 @ X21)
% 0.22/0.55          | (l1_orders_2 @ X20)
% 0.22/0.55          | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.22/0.55  thf('58', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('60', plain, ((l1_orders_2 @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('61', plain, ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      (![X20 : $i, X21 : $i]:
% 0.22/0.55         (~ (l1_waybel_0 @ X20 @ X21)
% 0.22/0.55          | (l1_orders_2 @ X20)
% 0.22/0.55          | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      ((~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | (l1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.55  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('65', plain, ((l1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (((m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | ~ (r1_tarski @ (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55             (u1_orders_2 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['55', '60', '65'])).
% 0.22/0.55  thf(dt_u1_orders_2, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_orders_2 @ A ) =>
% 0.22/0.55       ( m1_subset_1 @
% 0.22/0.55         ( u1_orders_2 @ A ) @ 
% 0.22/0.55         ( k1_zfmisc_1 @
% 0.22/0.55           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (u1_orders_2 @ X11) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X11))))
% 0.22/0.55          | ~ (l1_orders_2 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.22/0.55  thf(cc1_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( v1_relat_1 @ C ) ))).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.55         ((v1_relat_1 @ X4)
% 0.22/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.55  thf('70', plain,
% 0.22/0.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.55  thf('72', plain, ((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('73', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('74', plain,
% 0.22/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X33)
% 0.22/0.55          | ~ (l1_waybel_0 @ X33 @ X34)
% 0.22/0.55          | ~ (v6_waybel_0 @ X35 @ X34)
% 0.22/0.55          | ~ (l1_waybel_0 @ X35 @ X34)
% 0.22/0.55          | ((X35) != (k4_waybel_9 @ X34 @ X33 @ X36))
% 0.22/0.55          | (r2_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X35) @ 
% 0.22/0.55             (u1_orders_2 @ X35) @ 
% 0.22/0.55             (k1_toler_1 @ (u1_orders_2 @ X33) @ (u1_struct_0 @ X35)))
% 0.22/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X33))
% 0.22/0.55          | ~ (l1_struct_0 @ X34)
% 0.22/0.55          | (v2_struct_0 @ X34))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      (![X33 : $i, X34 : $i, X36 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X34)
% 0.22/0.55          | ~ (l1_struct_0 @ X34)
% 0.22/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X33))
% 0.22/0.55          | (r2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ X34 @ X33 @ X36)) @ 
% 0.22/0.55             (u1_struct_0 @ (k4_waybel_9 @ X34 @ X33 @ X36)) @ 
% 0.22/0.55             (u1_orders_2 @ (k4_waybel_9 @ X34 @ X33 @ X36)) @ 
% 0.22/0.55             (k1_toler_1 @ (u1_orders_2 @ X33) @ 
% 0.22/0.55              (u1_struct_0 @ (k4_waybel_9 @ X34 @ X33 @ X36))))
% 0.22/0.55          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X34 @ X33 @ X36) @ X34)
% 0.22/0.55          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X34 @ X33 @ X36) @ X34)
% 0.22/0.55          | ~ (l1_waybel_0 @ X33 @ X34)
% 0.22/0.55          | (v2_struct_0 @ X33))),
% 0.22/0.55      inference('simplify', [status(thm)], ['74'])).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_B)
% 0.22/0.55          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.22/0.55          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C) @ X0)
% 0.22/0.55          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C) @ X0)
% 0.22/0.55          | (r2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C)) @ 
% 0.22/0.55             (u1_struct_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C)) @ 
% 0.22/0.55             (u1_orders_2 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C)) @ 
% 0.22/0.55             (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55              (u1_struct_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C))))
% 0.22/0.55          | ~ (l1_struct_0 @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['73', '75'])).
% 0.22/0.55  thf('77', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | (r2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))
% 0.22/0.55        | ~ (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.22/0.55        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['72', '76'])).
% 0.22/0.55  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('79', plain, ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.55      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('80', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('81', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | (r2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))
% 0.22/0.55        | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.22/0.55  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('83', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | (r2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))))),
% 0.22/0.55      inference('clc', [status(thm)], ['81', '82'])).
% 0.22/0.55  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('85', plain,
% 0.22/0.55      ((r2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55        (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55        (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55        (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55         (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.55      inference('clc', [status(thm)], ['83', '84'])).
% 0.22/0.55  thf(dt_k1_toler_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( m1_subset_1 @
% 0.22/0.55         ( k1_toler_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) ) ) ))).
% 0.22/0.55  thf('86', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X16)
% 0.22/0.55          | (m1_subset_1 @ (k1_toler_1 @ X16 @ X17) @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17))))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k1_toler_1])).
% 0.22/0.55  thf('87', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (u1_orders_2 @ X11) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X11))))
% 0.22/0.55          | ~ (l1_orders_2 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.22/0.55  thf(redefinition_r2_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.22/0.55  thf('88', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.22/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.22/0.55          | ((X7) = (X10))
% 0.22/0.55          | ~ (r2_relset_1 @ X8 @ X9 @ X7 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.22/0.55  thf('89', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (l1_orders_2 @ X0)
% 0.22/0.55          | ~ (r2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.22/0.55               (u1_orders_2 @ X0) @ X1)
% 0.22/0.55          | ((u1_orders_2 @ X0) = (X1))
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.55  thf('90', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X1)
% 0.22/0.55          | ((u1_orders_2 @ X0) = (k1_toler_1 @ X1 @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ~ (r2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.22/0.55               (u1_orders_2 @ X0) @ (k1_toler_1 @ X1 @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ~ (l1_orders_2 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['86', '89'])).
% 0.22/0.55  thf('91', plain,
% 0.22/0.55      ((~ (l1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55        | ((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55            = (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55               (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))
% 0.22/0.55        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['85', '90'])).
% 0.22/0.55  thf('92', plain, ((l1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.22/0.55  thf('93', plain,
% 0.22/0.55      ((((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55          = (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))
% 0.22/0.55        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['91', '92'])).
% 0.22/0.55  thf('94', plain,
% 0.22/0.55      ((~ (l1_orders_2 @ sk_B)
% 0.22/0.55        | ((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55            = (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55               (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['71', '93'])).
% 0.22/0.55  thf('95', plain, ((l1_orders_2 @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('96', plain,
% 0.22/0.55      (((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55         = (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.22/0.55  thf(redefinition_k1_toler_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ( k1_toler_1 @ A @ B ) = ( k2_wellord1 @ A @ B ) ) ))).
% 0.22/0.55  thf('97', plain,
% 0.22/0.55      (![X18 : $i, X19 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X18)
% 0.22/0.55          | ((k1_toler_1 @ X18 @ X19) = (k2_wellord1 @ X18 @ X19)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k1_toler_1])).
% 0.22/0.55  thf('98', plain,
% 0.22/0.55      ((((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55          = (k2_wellord1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))
% 0.22/0.55        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_B)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['96', '97'])).
% 0.22/0.55  thf('99', plain,
% 0.22/0.55      ((~ (l1_orders_2 @ sk_B)
% 0.22/0.55        | ((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55            = (k2_wellord1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55               (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['70', '98'])).
% 0.22/0.55  thf('100', plain, ((l1_orders_2 @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('101', plain,
% 0.22/0.55      (((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55         = (k2_wellord1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.55      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.55  thf(d6_wellord1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( k2_wellord1 @ A @ B ) =
% 0.22/0.55           ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) ))).
% 0.22/0.55  thf('102', plain,
% 0.22/0.55      (![X2 : $i, X3 : $i]:
% 0.22/0.55         (((k2_wellord1 @ X2 @ X3)
% 0.22/0.55            = (k3_xboole_0 @ X2 @ (k2_zfmisc_1 @ X3 @ X3)))
% 0.22/0.55          | ~ (v1_relat_1 @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.22/0.55  thf(t17_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.55  thf('103', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.55  thf('104', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((r1_tarski @ (k2_wellord1 @ X1 @ X0) @ X1) | ~ (v1_relat_1 @ X1))),
% 0.22/0.55      inference('sup+', [status(thm)], ['102', '103'])).
% 0.22/0.55  thf('105', plain,
% 0.22/0.55      (((r1_tarski @ (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55         (u1_orders_2 @ sk_B))
% 0.22/0.55        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_B)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['101', '104'])).
% 0.22/0.55  thf('106', plain,
% 0.22/0.55      ((~ (l1_orders_2 @ sk_B)
% 0.22/0.55        | (r1_tarski @ (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55           (u1_orders_2 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['69', '105'])).
% 0.22/0.55  thf('107', plain, ((l1_orders_2 @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('108', plain,
% 0.22/0.55      ((r1_tarski @ (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.22/0.55        (u1_orders_2 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['106', '107'])).
% 0.22/0.55  thf('109', plain,
% 0.22/0.55      ((m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['66', '108'])).
% 0.22/0.55  thf('110', plain,
% 0.22/0.55      ((m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['42', '109'])).
% 0.22/0.55  thf('111', plain,
% 0.22/0.55      ((~ (m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B))
% 0.22/0.55         <= (~
% 0.22/0.55             ((m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('112', plain,
% 0.22/0.55      (((m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['110', '111'])).
% 0.22/0.55  thf('113', plain,
% 0.22/0.55      (~ ((v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)) | 
% 0.22/0.55       ~ ((m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('114', plain,
% 0.22/0.55      (~ ((v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['112', '113'])).
% 0.22/0.55  thf('115', plain,
% 0.22/0.55      (~ (v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['1', '114'])).
% 0.22/0.55  thf('116', plain,
% 0.22/0.55      ((m1_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['42', '109'])).
% 0.22/0.55  thf(d9_yellow_6, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_struct_0 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( l1_waybel_0 @ B @ A ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.22/0.55               ( ( v2_yellow_6 @ C @ A @ B ) <=>
% 0.22/0.55                 ( ( v4_yellow_0 @ C @ B ) & ( m1_yellow_0 @ C @ B ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('117', plain,
% 0.22/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.55         (~ (l1_waybel_0 @ X25 @ X26)
% 0.22/0.55          | ~ (v4_yellow_0 @ X27 @ X25)
% 0.22/0.55          | ~ (m1_yellow_0 @ X27 @ X25)
% 0.22/0.55          | (v2_yellow_6 @ X27 @ X26 @ X25)
% 0.22/0.55          | ~ (m1_yellow_6 @ X27 @ X26 @ X25)
% 0.22/0.55          | ~ (l1_struct_0 @ X26))),
% 0.22/0.55      inference('cnf', [status(esa)], [d9_yellow_6])).
% 0.22/0.55  thf('118', plain,
% 0.22/0.55      ((~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | (v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)
% 0.22/0.55        | ~ (m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | ~ (v4_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['116', '117'])).
% 0.22/0.55  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('120', plain,
% 0.22/0.55      ((m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['66', '108'])).
% 0.22/0.55  thf('121', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('122', plain,
% 0.22/0.55      (((v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)
% 0.22/0.55        | ~ (v4_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.22/0.55  thf('123', plain,
% 0.22/0.55      (((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55         = (k1_toler_1 @ (u1_orders_2 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.22/0.55  thf(d14_yellow_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_orders_2 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_yellow_0 @ B @ A ) =>
% 0.22/0.55           ( ( v4_yellow_0 @ B @ A ) <=>
% 0.22/0.55             ( ( u1_orders_2 @ B ) =
% 0.22/0.55               ( k1_toler_1 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ))).
% 0.22/0.55  thf('124', plain,
% 0.22/0.55      (![X14 : $i, X15 : $i]:
% 0.22/0.55         (~ (m1_yellow_0 @ X14 @ X15)
% 0.22/0.55          | ((u1_orders_2 @ X14)
% 0.22/0.55              != (k1_toler_1 @ (u1_orders_2 @ X15) @ (u1_struct_0 @ X14)))
% 0.22/0.55          | (v4_yellow_0 @ X14 @ X15)
% 0.22/0.55          | ~ (l1_orders_2 @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [d14_yellow_0])).
% 0.22/0.55  thf('125', plain,
% 0.22/0.55      ((((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55          != (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.55        | ~ (l1_orders_2 @ sk_B)
% 0.22/0.55        | (v4_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | ~ (m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['123', '124'])).
% 0.22/0.55  thf('126', plain, ((l1_orders_2 @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('127', plain,
% 0.22/0.55      ((((u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))
% 0.22/0.55          != (u1_orders_2 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.55        | (v4_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | ~ (m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['125', '126'])).
% 0.22/0.55  thf('128', plain,
% 0.22/0.55      ((~ (m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 0.22/0.55        | (v4_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 0.22/0.55      inference('simplify', [status(thm)], ['127'])).
% 0.22/0.55  thf('129', plain,
% 0.22/0.55      ((m1_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['66', '108'])).
% 0.22/0.55  thf('130', plain,
% 0.22/0.55      ((v4_yellow_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['128', '129'])).
% 0.22/0.55  thf('131', plain,
% 0.22/0.55      ((v2_yellow_6 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A @ sk_B)),
% 0.22/0.55      inference('demod', [status(thm)], ['122', '130'])).
% 0.22/0.55  thf('132', plain, ($false), inference('demod', [status(thm)], ['115', '131'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
