%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aFKUhtlzOr

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 146 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   32
%              Number of atoms          :  891 (1631 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('1',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(rc20_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ( v1_zfmisc_1 @ B )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('7',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('9',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

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

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_E @ X13 @ X14 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_waybel_0 @ X12 @ X11 @ X14 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_struct_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_struct_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( l1_orders_2 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('20',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(dt_k2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X18 @ X17 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X12 @ X11 @ ( sk_E @ X13 @ X14 @ X11 @ X12 ) ) @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_waybel_0 @ X12 @ X11 @ X14 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['6','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ~ ( l1_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( l1_orders_2 @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ~ ( l1_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( l1_orders_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aFKUhtlzOr
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:07:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 50 iterations in 0.039s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.50  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.50  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.50  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.50  thf(dt_l1_orders_2, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('0', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.50  thf('1', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.50  thf(d1_xboole_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf(rc20_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ?[B:$i]:
% 0.21/0.50         ( ( v1_zfmisc_1 @ B ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.50           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X9 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (sk_B_1 @ X9) @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.50          | ~ (l1_struct_0 @ X9)
% 0.21/0.50          | (v2_struct_0 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [rc20_struct_0])).
% 0.21/0.50  thf(t4_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.50          | (m1_subset_1 @ X5 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.21/0.50          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.50  thf(t29_yellow_6, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.21/0.50  thf('7', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.50  thf('9', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.21/0.50          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.50  thf(d11_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.50               ( ?[D:$i]:
% 0.21/0.50                 ( ( ![E:$i]:
% 0.21/0.50                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.21/0.50                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.21/0.50                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X11)
% 0.21/0.50          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.21/0.50          | (m1_subset_1 @ (sk_E @ X13 @ X14 @ X11 @ X12) @ (u1_struct_0 @ X11))
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.21/0.50          | (r1_waybel_0 @ X12 @ X11 @ X14)
% 0.21/0.50          | ~ (l1_struct_0 @ X12)
% 0.21/0.50          | (v2_struct_0 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (l1_struct_0 @ X1)
% 0.21/0.50          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.50          | (m1_subset_1 @ (sk_E @ (sk_B @ (sk_B_1 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.50             (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.50          | (m1_subset_1 @ (sk_E @ (sk_B @ (sk_B_1 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.50             (u1_struct_0 @ X0))
% 0.21/0.50          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.50          | ~ (l1_struct_0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_2)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_B_2)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '13'])).
% 0.21/0.50  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_2)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_B_2)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B_2)))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_B_2)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B_2))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '16'])).
% 0.21/0.50  thf('18', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l1_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_struct_0 @ A ) =>
% 0.21/0.50       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i]:
% 0.21/0.50         (~ (l1_waybel_0 @ X20 @ X21)
% 0.21/0.50          | (l1_orders_2 @ X20)
% 0.21/0.50          | ~ (l1_struct_0 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.50  thf('20', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain, ((l1_orders_2 @ sk_B_2)),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((m1_subset_1 @ 
% 0.21/0.50           (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.50           (u1_struct_0 @ sk_B_2))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('demod', [status(thm)], ['17', '22'])).
% 0.21/0.50  thf(dt_k2_waybel_0, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.50         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.50          | (v2_struct_0 @ X17)
% 0.21/0.50          | ~ (l1_struct_0 @ X18)
% 0.21/0.50          | (v2_struct_0 @ X18)
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.50          | (m1_subset_1 @ (k2_waybel_0 @ X18 @ X17 @ X19) @ 
% 0.21/0.50             (u1_struct_0 @ X18)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_2)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.50             (u1_struct_0 @ X1))
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (l1_struct_0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_B_2)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B_2 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.21/0.50          | ~ (l1_struct_0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.50             (u1_struct_0 @ X1))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_2)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '26'])).
% 0.21/0.50  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_2)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((m1_subset_1 @ 
% 0.21/0.50           (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.50            (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.50           (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.50  thf(t2_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((r2_hidden @ X3 @ X4)
% 0.21/0.50          | (v1_xboole_0 @ X4)
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_2)
% 0.21/0.50          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (sk_B_1 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X11)
% 0.21/0.50          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.21/0.50          | ~ (r2_hidden @ 
% 0.21/0.50               (k2_waybel_0 @ X12 @ X11 @ (sk_E @ X13 @ X14 @ X11 @ X12)) @ X14)
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.21/0.50          | (r1_waybel_0 @ X12 @ X11 @ X14)
% 0.21/0.50          | ~ (l1_struct_0 @ X12)
% 0.21/0.50          | (v2_struct_0 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_B_2)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_B @ (sk_B_1 @ sk_B_2)) @ (u1_struct_0 @ sk_B_2))
% 0.21/0.50        | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('36', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_B_2)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_B @ (sk_B_1 @ sk_B_2)) @ (u1_struct_0 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((~ (m1_subset_1 @ (sk_B @ (sk_B_1 @ sk_B_2)) @ (u1_struct_0 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_B_2)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_2)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_B_2)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_B_2)
% 0.21/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      ((~ (l1_orders_2 @ sk_B_2)
% 0.21/0.50        | (v2_struct_0 @ sk_B_2)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '40'])).
% 0.21/0.50  thf('42', plain, ((l1_orders_2 @ sk_B_2)),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_2)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf(fc2_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X8 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.21/0.50          | ~ (l1_struct_0 @ X8)
% 0.21/0.50          | (v2_struct_0 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_2)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_2)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.21/0.50        | (v2_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.50  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_2) | (v1_xboole_0 @ (sk_B_1 @ sk_B_2)))),
% 0.21/0.50      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_B_2))),
% 0.21/0.50      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X9 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (sk_B_1 @ X9))
% 0.21/0.50          | ~ (l1_struct_0 @ X9)
% 0.21/0.50          | (v2_struct_0 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [rc20_struct_0])).
% 0.21/0.50  thf('56', plain, (((v2_struct_0 @ sk_B_2) | ~ (l1_struct_0 @ sk_B_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('58', plain, (~ (l1_struct_0 @ sk_B_2)),
% 0.21/0.51      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.51  thf('59', plain, (~ (l1_orders_2 @ sk_B_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '58'])).
% 0.21/0.51  thf('60', plain, ((l1_orders_2 @ sk_B_2)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('61', plain, ($false), inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
