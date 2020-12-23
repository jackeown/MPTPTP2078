%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WgCpCTzEDE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:02 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 194 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   29
%              Number of atoms          : 1050 (2499 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   24 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( r1_waybel_0 @ X24 @ X23 @ ( k6_subset_1 @ ( u1_struct_0 @ X24 ) @ X25 ) )
      | ( r2_waybel_0 @ X24 @ X23 @ X25 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( r1_waybel_0 @ X24 @ X23 @ ( k4_xboole_0 @ ( u1_struct_0 @ X24 ) @ X25 ) )
      | ( r2_waybel_0 @ X24 @ X23 @ X25 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( m1_subset_1 @ ( sk_D @ X19 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ( r2_waybel_0 @ X18 @ X17 @ X19 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X17: $i,X18: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r2_waybel_0 @ X18 @ X17 @ X21 )
      | ( r2_hidden @ ( k2_waybel_0 @ X18 @ X17 @ ( sk_E @ X22 @ X21 @ X17 @ X18 ) ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X1 @ sk_B_1 @ sk_A ) @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X1 @ sk_B_1 @ sk_A ) @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('38',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r2_waybel_0 @ X18 @ X17 @ X21 )
      | ( m1_subset_1 @ ( sk_E @ X22 @ X21 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r2_waybel_0 @ X18 @ X17 @ X21 )
      | ( r2_hidden @ ( k2_waybel_0 @ X18 @ X17 @ ( sk_E @ X22 @ X21 @ X17 @ X18 ) ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X2 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X2 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X2 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(condensation,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WgCpCTzEDE
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 152 iterations in 0.128s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.39/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.58  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.39/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.58  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.39/0.58  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.39/0.58  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.39/0.58  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.39/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.58  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf(t3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.58  thf(existence_m1_subset_1, axiom,
% 0.39/0.58    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.39/0.58  thf('2', plain, (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.39/0.58      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.39/0.58  thf(t5_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.39/0.58          ( v1_xboole_0 @ C ) ) ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X14 @ X15)
% 0.39/0.58          | ~ (v1_xboole_0 @ X16)
% 0.39/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X0)
% 0.39/0.58          | ~ (r2_hidden @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r1_xboole_0 @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0)))
% 0.39/0.58          | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '4'])).
% 0.39/0.58  thf(t83_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X0)
% 0.39/0.58          | ((k4_xboole_0 @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0))) = (X1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.58  thf(t29_yellow_6, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.39/0.58             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.39/0.58           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.39/0.58                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.39/0.58              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.39/0.58  thf('8', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t10_waybel_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.39/0.58               ( ~( r1_waybel_0 @
% 0.39/0.58                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X23)
% 0.39/0.58          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.39/0.58          | (r1_waybel_0 @ X24 @ X23 @ 
% 0.39/0.58             (k6_subset_1 @ (u1_struct_0 @ X24) @ X25))
% 0.39/0.58          | (r2_waybel_0 @ X24 @ X23 @ X25)
% 0.39/0.58          | ~ (l1_struct_0 @ X24)
% 0.39/0.58          | (v2_struct_0 @ X24))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.39/0.58  thf(redefinition_k6_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X23)
% 0.39/0.59          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.39/0.59          | (r1_waybel_0 @ X24 @ X23 @ 
% 0.39/0.59             (k4_xboole_0 @ (u1_struct_0 @ X24) @ X25))
% 0.39/0.59          | (r2_waybel_0 @ X24 @ X23 @ X25)
% 0.39/0.59          | ~ (l1_struct_0 @ X24)
% 0.39/0.59          | (v2_struct_0 @ X24))),
% 0.39/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (l1_struct_0 @ sk_A)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.39/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '11'])).
% 0.39/0.59  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.39/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.59          | ~ (v1_xboole_0 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (k1_zfmisc_1 @ X0)))
% 0.39/0.59          | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup+', [status(thm)], ['7', '14'])).
% 0.39/0.59  thf('16', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (k1_zfmisc_1 @ X0)))
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.59  thf('18', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('19', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d12_waybel_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.39/0.59                   ( ?[E:$i]:
% 0.39/0.59                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.39/0.59                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.39/0.59                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X17)
% 0.39/0.59          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.39/0.59          | (m1_subset_1 @ (sk_D @ X19 @ X17 @ X18) @ (u1_struct_0 @ X17))
% 0.39/0.59          | (r2_waybel_0 @ X18 @ X17 @ X19)
% 0.39/0.59          | ~ (l1_struct_0 @ X18)
% 0.39/0.59          | (v2_struct_0 @ X18))),
% 0.39/0.59      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (l1_struct_0 @ sk_A)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.39/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.59  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.39/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.39/0.59      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X21 : $i, X22 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X17)
% 0.39/0.59          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.39/0.59          | ~ (r2_waybel_0 @ X18 @ X17 @ X21)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ X18 @ X17 @ (sk_E @ X22 @ X21 @ X17 @ X18)) @ X21)
% 0.39/0.59          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X17))
% 0.39/0.59          | ~ (l1_struct_0 @ X18)
% 0.39/0.59          | (v2_struct_0 @ X18))),
% 0.39/0.59      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ X1)
% 0.39/0.59          | ~ (l1_struct_0 @ X1)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.39/0.59             X2)
% 0.39/0.59          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.39/0.59          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.39/0.59          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.39/0.59             X2)
% 0.39/0.59          | ~ (l1_struct_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.39/0.59      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (l1_struct_0 @ sk_A)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59             X1)
% 0.39/0.59          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '26'])).
% 0.39/0.59  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59             X1)
% 0.39/0.59          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.39/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59             X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.39/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ (sk_D @ X1 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59               (sk_B @ (k1_zfmisc_1 @ X0)) @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59             (sk_B @ (k1_zfmisc_1 @ X0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['17', '30'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r2_hidden @ 
% 0.39/0.59           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59            (sk_E @ (sk_D @ X1 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59             (sk_B @ (k1_zfmisc_1 @ X0)) @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59           (sk_B @ (k1_zfmisc_1 @ X0)))
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X0)
% 0.39/0.59          | ~ (r2_hidden @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['34'])).
% 0.39/0.59  thf('36', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['34'])).
% 0.39/0.59  thf('38', plain, (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.39/0.59      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X21 : $i, X22 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X17)
% 0.39/0.59          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.39/0.59          | ~ (r2_waybel_0 @ X18 @ X17 @ X21)
% 0.39/0.59          | (m1_subset_1 @ (sk_E @ X22 @ X21 @ X17 @ X18) @ (u1_struct_0 @ X17))
% 0.39/0.59          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X17))
% 0.39/0.59          | ~ (l1_struct_0 @ X18)
% 0.39/0.59          | (v2_struct_0 @ X18))),
% 0.39/0.59      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X1)
% 0.39/0.59          | ~ (l1_struct_0 @ X1)
% 0.39/0.59          | (m1_subset_1 @ 
% 0.39/0.59             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.39/0.59             (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.39/0.59          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.39/0.59          | (m1_subset_1 @ 
% 0.39/0.59             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59             (u1_struct_0 @ sk_B_1))
% 0.39/0.59          | ~ (l1_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['37', '40'])).
% 0.39/0.59  thf('42', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (m1_subset_1 @ 
% 0.39/0.59             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59             (u1_struct_0 @ sk_B_1))
% 0.39/0.59          | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((m1_subset_1 @ 
% 0.39/0.59           (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59           (u1_struct_0 @ sk_B_1))
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X21 : $i, X22 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X17)
% 0.39/0.59          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.39/0.59          | ~ (r2_waybel_0 @ X18 @ X17 @ X21)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ X18 @ X17 @ (sk_E @ X22 @ X21 @ X17 @ X18)) @ X21)
% 0.39/0.59          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X17))
% 0.39/0.59          | ~ (l1_struct_0 @ X18)
% 0.39/0.59          | (v2_struct_0 @ X18))),
% 0.39/0.59      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X3)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ X1)
% 0.39/0.59          | ~ (l1_struct_0 @ X1)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ 
% 0.39/0.59               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59               X2 @ sk_B_1 @ X1)) @ 
% 0.39/0.59             X2)
% 0.39/0.59          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.39/0.59          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.39/0.59          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ 
% 0.39/0.59               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59               X2 @ sk_B_1 @ X1)) @ 
% 0.39/0.59             X2)
% 0.39/0.59          | ~ (l1_struct_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X3))),
% 0.39/0.59      inference('simplify', [status(thm)], ['47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (l1_struct_0 @ sk_A)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ 
% 0.39/0.59               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X2 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59               X1 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59             X1)
% 0.39/0.59          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['36', '48'])).
% 0.39/0.59  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X0)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ 
% 0.39/0.59               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X2 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59               X1 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59             X1)
% 0.39/0.59          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.39/0.59      inference('demod', [status(thm)], ['49', '50'])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ 
% 0.39/0.59               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X2 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59               X1 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59             X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['51'])).
% 0.39/0.59  thf('53', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X3)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (v1_xboole_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (r2_hidden @ 
% 0.39/0.59             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59              (sk_E @ 
% 0.39/0.59               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X2 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59               X0 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59             X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['35', '52'])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         ((r2_hidden @ 
% 0.39/0.59           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.39/0.59            (sk_E @ 
% 0.39/0.59             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X2 @ sk_B_1 @ sk_A) @ 
% 0.39/0.59             X0 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.59           X0)
% 0.39/0.59          | ~ (v1_xboole_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | ~ (v1_xboole_0 @ X3))),
% 0.39/0.59      inference('simplify', [status(thm)], ['53'])).
% 0.39/0.59  thf(t4_subset_1, axiom,
% 0.39/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.59  thf('55', plain,
% 0.39/0.59      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.59  thf('56', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X14 @ X15)
% 0.39/0.59          | ~ (v1_xboole_0 @ X16)
% 0.39/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.59  thf('58', plain,
% 0.39/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X2)
% 0.39/0.59          | (v2_struct_0 @ sk_B_1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (v1_xboole_0 @ X3)
% 0.39/0.59          | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['54', '57'])).
% 0.39/0.59  thf('59', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X0)
% 0.39/0.59          | ~ (v1_xboole_0 @ X1)
% 0.39/0.59          | (v2_struct_0 @ sk_A)
% 0.39/0.59          | ~ (v1_xboole_0 @ X2))),
% 0.39/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.59  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('62', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2))),
% 0.39/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.59  thf('63', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('condensation', [status(thm)], ['62'])).
% 0.39/0.59  thf('64', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.39/0.59      inference('condensation', [status(thm)], ['63'])).
% 0.39/0.59  thf('65', plain, ($false), inference('sup-', [status(thm)], ['0', '64'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
