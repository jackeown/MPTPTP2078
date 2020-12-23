%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8rillhiAtg

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 236 expanded)
%              Number of leaves         :   35 (  85 expanded)
%              Depth                    :   25
%              Number of atoms          :  888 (2722 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('1',plain,(
    ! [X8: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('2',plain,(
    ! [X8: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

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

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
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

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ( r1_waybel_0 @ X25 @ X24 @ ( k6_subset_1 @ ( u1_struct_0 @ X25 ) @ X26 ) )
      | ( r2_waybel_0 @ X25 @ X24 @ X26 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ( r1_waybel_0 @ X25 @ X24 @ ( k4_xboole_0 @ ( u1_struct_0 @ X25 ) @ X26 ) )
      | ( r2_waybel_0 @ X25 @ X24 @ X26 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
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

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( m1_subset_1 @ ( sk_D @ X20 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r2_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( r2_waybel_0 @ X19 @ X18 @ X22 )
      | ( r2_hidden @ ( k2_waybel_0 @ X19 @ X18 @ ( sk_E @ X23 @ X22 @ X18 @ X19 ) ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ X2 @ sk_B_2 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_2 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_2 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ X2 @ sk_B_2 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ X1 @ sk_B_2 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ X1 @ sk_B_2 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ X1 @ sk_B_2 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ k1_xboole_0 @ sk_B_2 @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X1: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('47',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( r2_waybel_0 @ X19 @ X18 @ X22 )
      | ( m1_subset_1 @ ( sk_E @ X23 @ X22 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X18: $i,X19: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( r2_waybel_0 @ X19 @ X18 @ X22 )
      | ( r2_hidden @ ( k2_waybel_0 @ X19 @ X18 @ ( sk_E @ X23 @ X22 @ X18 @ X19 ) ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ X2 @ sk_B_2 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_2 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf('61',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('69',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8rillhiAtg
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 138 iterations in 0.099s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.56  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.56  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.56  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.56  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.56  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.21/0.56  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(rc2_subset_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ?[B:$i]:
% 0.21/0.56       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.56  thf('0', plain, (![X8 : $i]: (v1_xboole_0 @ (sk_B_1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.56  thf('1', plain, (![X8 : $i]: (v1_xboole_0 @ (sk_B_1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.56  thf('2', plain, (![X8 : $i]: (v1_xboole_0 @ (sk_B_1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.56  thf(t3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf(t4_subset_1, axiom,
% 0.21/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.56  thf(t5_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X15 @ X16)
% 0.21/0.56          | ~ (v1_xboole_0 @ X17)
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.56  thf('8', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.56  thf(t83_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.56  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf(t29_yellow_6, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.56             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.56           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.56                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.56              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.21/0.56  thf('11', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t10_waybel_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.56               ( ~( r1_waybel_0 @
% 0.21/0.56                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X24)
% 0.21/0.56          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.21/0.56          | (r1_waybel_0 @ X25 @ X24 @ 
% 0.21/0.56             (k6_subset_1 @ (u1_struct_0 @ X25) @ X26))
% 0.21/0.56          | (r2_waybel_0 @ X25 @ X24 @ X26)
% 0.21/0.56          | ~ (l1_struct_0 @ X25)
% 0.21/0.56          | (v2_struct_0 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.21/0.56  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i]:
% 0.21/0.56         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X24)
% 0.21/0.56          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.21/0.56          | (r1_waybel_0 @ X25 @ X24 @ 
% 0.21/0.56             (k4_xboole_0 @ (u1_struct_0 @ X25) @ X26))
% 0.21/0.56          | (r2_waybel_0 @ X25 @ X24 @ X26)
% 0.21/0.56          | ~ (l1_struct_0 @ X25)
% 0.21/0.56          | (v2_struct_0 @ X25))),
% 0.21/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.56          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.56  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.56          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (((r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | (v2_struct_0 @ sk_B_2)
% 0.21/0.56        | (r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['10', '17'])).
% 0.21/0.56  thf('19', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | (r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0)
% 0.21/0.56        | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B_2) | (r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0))),
% 0.21/0.56      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf('23', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('24', plain, ((r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0)),
% 0.21/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('25', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d12_waybel_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.56                   ( ?[E:$i]:
% 0.21/0.56                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.21/0.56                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.21/0.56                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X18)
% 0.21/0.56          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ X20 @ X18 @ X19) @ (u1_struct_0 @ X18))
% 0.21/0.56          | (r2_waybel_0 @ X19 @ X18 @ X20)
% 0.21/0.56          | ~ (l1_struct_0 @ X19)
% 0.21/0.56          | (v2_struct_0 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 0.21/0.56          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_B_2))
% 0.21/0.56          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X22 : $i, X23 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X18)
% 0.21/0.56          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.56          | ~ (r2_waybel_0 @ X19 @ X18 @ X22)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ X19 @ X18 @ (sk_E @ X23 @ X22 @ X18 @ X19)) @ X22)
% 0.21/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.21/0.56          | ~ (l1_struct_0 @ X19)
% 0.21/0.56          | (v2_struct_0 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ X1)
% 0.21/0.56          | ~ (l1_struct_0 @ X1)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ X2 @ sk_B_2 @ X1)) @ 
% 0.21/0.56             X2)
% 0.21/0.56          | ~ (r2_waybel_0 @ X1 @ sk_B_2 @ X2)
% 0.21/0.56          | ~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.21/0.56          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.21/0.56          | ~ (r2_waybel_0 @ X1 @ sk_B_2 @ X2)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ X2 @ sk_B_2 @ X1)) @ 
% 0.21/0.56             X2)
% 0.21/0.56          | ~ (l1_struct_0 @ X1)
% 0.21/0.56          | (v2_struct_0 @ X1)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ X1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.56             X1)
% 0.21/0.56          | ~ (r2_waybel_0 @ sk_A @ sk_B_2 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '33'])).
% 0.21/0.56  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ X1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.56             X1)
% 0.21/0.56          | ~ (r2_waybel_0 @ sk_A @ sk_B_2 @ X1))),
% 0.21/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ X1 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.56             X1)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ k1_xboole_0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.56             k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (v2_struct_0 @ sk_B_2)
% 0.21/0.56          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '40'])).
% 0.21/0.56  thf('42', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X1 : $i]: ((v2_struct_0 @ sk_A) | (r2_waybel_0 @ sk_A @ sk_B_2 @ X1))),
% 0.21/0.56      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.56  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain, (![X1 : $i]: (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)),
% 0.21/0.56      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain, (![X1 : $i]: (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)),
% 0.21/0.56      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf(existence_m1_subset_1, axiom,
% 0.21/0.56    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.21/0.56  thf('47', plain, (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.21/0.56      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X22 : $i, X23 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X18)
% 0.21/0.56          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.56          | ~ (r2_waybel_0 @ X19 @ X18 @ X22)
% 0.21/0.56          | (m1_subset_1 @ (sk_E @ X23 @ X22 @ X18 @ X19) @ (u1_struct_0 @ X18))
% 0.21/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.21/0.56          | ~ (l1_struct_0 @ X19)
% 0.21/0.56          | (v2_struct_0 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X1)
% 0.21/0.56          | ~ (l1_struct_0 @ X1)
% 0.21/0.56          | (m1_subset_1 @ 
% 0.21/0.56             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.56             (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.56          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.56          | (v2_struct_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.21/0.56          | (m1_subset_1 @ 
% 0.21/0.56             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56             (u1_struct_0 @ sk_B_2))
% 0.21/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.56  thf('51', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | (m1_subset_1 @ 
% 0.21/0.56             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56             (u1_struct_0 @ sk_B_2))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.56  thf('54', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | (m1_subset_1 @ 
% 0.21/0.56             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56             (u1_struct_0 @ sk_B_2)))),
% 0.21/0.56      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (m1_subset_1 @ 
% 0.21/0.56          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56          (u1_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X22 : $i, X23 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X18)
% 0.21/0.56          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.56          | ~ (r2_waybel_0 @ X19 @ X18 @ X22)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ X19 @ X18 @ (sk_E @ X23 @ X22 @ X18 @ X19)) @ X22)
% 0.21/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.21/0.56          | ~ (l1_struct_0 @ X19)
% 0.21/0.56          | (v2_struct_0 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X1)
% 0.21/0.56          | ~ (l1_struct_0 @ X1)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ 
% 0.21/0.56               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56               X2 @ sk_B_2 @ X1)) @ 
% 0.21/0.56             X2)
% 0.21/0.56          | ~ (r2_waybel_0 @ X1 @ sk_B_2 @ X2)
% 0.21/0.56          | ~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.21/0.56          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ 
% 0.21/0.56               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X1 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56               X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.56             X0)
% 0.21/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['45', '59'])).
% 0.21/0.56  thf('61', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_B_2)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ 
% 0.21/0.56               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X1 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56               X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.56             X0)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.56  thf('64', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (sk_E @ 
% 0.21/0.56               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X1 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56               X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.56             X0))),
% 0.21/0.56      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.56  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (r2_hidden @ 
% 0.21/0.56          (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.56           (sk_E @ 
% 0.21/0.56            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X1 @ sk_B_2 @ sk_A) @ 
% 0.21/0.56            X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.56          X0)),
% 0.21/0.56      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('69', plain, (![X1 : $i]: ~ (v1_xboole_0 @ X1)),
% 0.21/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.56  thf('70', plain, ($false), inference('sup-', [status(thm)], ['0', '69'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
