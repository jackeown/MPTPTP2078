%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1976+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FFzJRNsyOG

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  229 (3037 expanded)
%              Number of leaves         :   50 (1055 expanded)
%              Depth                    :   29
%              Number of atoms          : 2262 (32606 expanded)
%              Number of equality atoms :   56 (1524 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v11_waybel_1_type,type,(
    v11_waybel_1: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_yellow_0_type,type,(
    v3_yellow_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v10_waybel_1_type,type,(
    v10_waybel_1: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v2_waybel_7_type,type,(
    v2_waybel_7: $i > $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_waybel_1_type,type,(
    k7_waybel_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v2_waybel_1_type,type,(
    v2_waybel_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(t25_waybel_7,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
        & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
     => ( ( v2_waybel_7 @ B @ ( k3_yellow_1 @ A ) )
      <=> ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r2_hidden @ C @ B )
              | ( r2_hidden @ ( k6_subset_1 @ A @ C ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ~ ( v1_xboole_0 @ B )
          & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
          & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
       => ( ( v2_waybel_7 @ B @ ( k3_yellow_1 @ A ) )
        <=> ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
             => ( ( r2_hidden @ C @ B )
                | ( r2_hidden @ ( k6_subset_1 @ A @ C ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_waybel_7])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
    | ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ X30 @ sk_B )
      | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B )
      | ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t24_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v11_waybel_1 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_waybel_7 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                  | ( r2_hidden @ ( k7_waybel_1 @ A @ C ) @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ X23 )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ( v2_waybel_7 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v11_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_7])).

thf('9',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ X23 )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k9_setfam_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ( v2_waybel_7 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v11_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v3_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v4_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) @ ( u1_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(fc7_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ~ ( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('13',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('14',plain,(
    ! [X14: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X15: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('16',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('17',plain,(
    ! [X15: $i] :
      ( v4_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('19',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('20',plain,(
    ! [X16: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(fc1_waybel_7,axiom,(
    ! [A: $i] :
      ( ( v11_waybel_1 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( v11_waybel_1 @ ( k3_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_waybel_7])).

thf('22',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('23',plain,(
    ! [X11: $i] :
      ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i] :
      ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(cc8_waybel_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v11_waybel_1 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_yellow_0 @ A )
          & ( v2_waybel_1 @ A )
          & ( v10_waybel_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_waybel_1 @ X1 )
      | ( v1_lattice3 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc8_waybel_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('30',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('31',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X11: $i] :
      ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('34',plain,(
    ! [X9: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v11_waybel_1 @ X1 )
      | ( v2_lattice3 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc8_waybel_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X12: $i] :
      ~ ( v2_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('41',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('43',plain,(
    v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('46',plain,(
    v2_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) @ ( u1_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','14','17','20','23','32','39','40','43','46'])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A )
      & ( v8_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v4_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf('50',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('51',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X7 ) @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( g1_orders_2 @ X19 @ X20 )
       != ( g1_orders_2 @ X17 @ X18 ) )
      | ( X19 = X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('53',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('54',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( g1_orders_2 @ X19 @ X20 )
       != ( g1_orders_2 @ X17 @ X18 ) )
      | ( X19 = X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf(d1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k2_yellow_1 @ A )
      = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X2: $i] :
      ( ( k2_yellow_1 @ X2 )
      = ( g1_orders_2 @ X2 @ ( k1_yellow_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X9: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('61',plain,(
    ! [X8: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('62',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) @ ( k9_setfam_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) @ ( k9_setfam_1 @ sk_A ) )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('67',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('68',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k9_setfam_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) @ sk_B ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) @ ( k9_setfam_1 @ sk_A ) )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf(t9_waybel_7,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
     => ( ( k7_waybel_1 @ ( k3_yellow_1 @ A ) @ B )
        = ( k6_subset_1 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_waybel_1 @ ( k3_yellow_1 @ X28 ) @ X29 )
        = ( k6_subset_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k3_yellow_1 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_7])).

thf('72',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('73',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('74',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X28 ) ) @ X29 )
        = ( k6_subset_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X28 ) ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['59','60','61'])).

thf('76',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X28 ) ) @ X29 )
        = ( k6_subset_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k9_setfam_1 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) )
      = ( k6_subset_1 @ sk_A @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['59','60','61'])).

thf('79',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ X23 )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r2_hidden @ ( k7_waybel_1 @ X23 @ ( sk_C @ X22 @ X23 ) ) @ X22 )
      | ( v2_waybel_7 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v11_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_7])).

thf('80',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('81',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ X23 )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k9_setfam_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r2_hidden @ ( k7_waybel_1 @ X23 @ ( sk_C @ X22 @ X23 ) ) @ X22 )
      | ( v2_waybel_7 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v11_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_waybel_7 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k7_waybel_1 @ ( k2_yellow_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_yellow_1 @ X0 ) ) ) @ X1 )
      | ~ ( v13_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X9: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_waybel_7 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k7_waybel_1 @ ( k2_yellow_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_yellow_1 @ X0 ) ) ) @ X1 )
      | ~ ( v13_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) @ sk_B )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v4_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( v3_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,(
    v2_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('87',plain,(
    v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('88',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('89',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('90',plain,(
    ! [X11: $i] :
      ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('91',plain,(
    ! [X16: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('92',plain,(
    ! [X15: $i] :
      ( v4_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('93',plain,(
    ! [X14: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('95',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['59','60','61'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) @ sk_B )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92','93','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) @ sk_B )
    | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) @ sk_B )
      | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','100'])).

thf('102',plain,
    ( ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) @ sk_B ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['59','60','61'])).

thf('104',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ X23 )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X22 @ X23 ) @ X22 )
      | ( v2_waybel_7 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v11_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_7])).

thf('105',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('106',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ X23 )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k9_setfam_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X22 @ X23 ) @ X22 )
      | ( v2_waybel_7 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v11_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_waybel_7 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X1 )
      | ~ ( v13_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X9: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_waybel_7 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X1 )
      | ~ ( v13_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,(
    v2_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('112',plain,(
    v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('113',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('114',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('115',plain,(
    ! [X11: $i] :
      ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('116',plain,(
    ! [X16: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('117',plain,(
    ! [X15: $i] :
      ( v4_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('118',plain,(
    ! [X14: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('120',plain,
    ( ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115','116','117','118','119'])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
        | ( r2_hidden @ X30 @ sk_B )
        | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('125',plain,
    ( ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
   <= ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('126',plain,
    ( ~ ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
   <= ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ sk_A ) )
          | ( r2_hidden @ X30 @ sk_B )
          | ( r2_hidden @ ( k6_subset_1 @ sk_A @ X30 ) @ sk_B ) )
    | ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
    | ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('129',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','127','128'])).

thf('130',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','129'])).

thf('131',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['131'])).

thf('133',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('134',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['131'])).

thf('136',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','127','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['134','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('139',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['59','60','61'])).

thf('140',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ X23 )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_waybel_7 @ X22 @ X23 )
      | ( r2_hidden @ ( k7_waybel_1 @ X23 @ X24 ) @ X22 )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v11_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_7])).

thf('141',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('142',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ X23 )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k9_setfam_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_waybel_7 @ X22 @ X23 )
      | ( r2_hidden @ ( k7_waybel_1 @ X23 @ X24 ) @ X22 )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v1_lattice3 @ X23 )
      | ~ ( v11_waybel_1 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k7_waybel_1 @ ( k2_yellow_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v2_waybel_7 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X9: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('145',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['59','60','61'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k7_waybel_1 @ ( k2_yellow_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v2_waybel_7 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v2_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ X0 ) @ sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['138','146'])).

thf('148',plain,(
    v2_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('149',plain,(
    v13_waybel_0 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('150',plain,
    ( ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
   <= ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('151',plain,(
    ! [X25: $i] :
      ( ( k3_yellow_1 @ X25 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('152',plain,
    ( ( v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) )
   <= ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','127'])).

thf('154',plain,(
    v2_waybel_7 @ sk_B @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_lattice3 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('157',plain,(
    ! [X11: $i] :
      ( v11_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('158',plain,(
    ! [X16: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('159',plain,(
    ! [X15: $i] :
      ( v4_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('160',plain,(
    ! [X14: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ X0 ) @ sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['147','148','149','154','155','156','157','158','159','160'])).

thf('162',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['137','161'])).

thf('163',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('164',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X28 ) ) @ X29 )
        = ( k6_subset_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k9_setfam_1 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('165',plain,
    ( ( ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_C_1 )
      = ( k6_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','127','135'])).

thf('167',plain,
    ( ( k7_waybel_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_C_1 )
    = ( k6_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['162','167'])).

thf('169',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
   <= ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['169'])).

thf('171',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v2_waybel_7 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['169'])).

thf('172',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','127','171'])).

thf('173',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['170','172'])).

thf('174',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(clc,[status(thm)],['168','173'])).

thf('175',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    r2_hidden @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['130','176'])).


%------------------------------------------------------------------------------
