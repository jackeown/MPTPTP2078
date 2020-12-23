%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1966+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sE1E5YORjp

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:37 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  326 (10481 expanded)
%              Number of leaves         :   56 (3479 expanded)
%              Depth                    :   34
%              Number of atoms          : 3192 (130938 expanded)
%              Number of equality atoms :  102 (3130 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v9_waybel_1_type,type,(
    v9_waybel_1: $i > $o )).

thf(v11_waybel_1_type,type,(
    v11_waybel_1: $i > $o )).

thf(v2_yellow_0_type,type,(
    v2_yellow_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_yellow_0_type,type,(
    v3_yellow_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v10_waybel_1_type,type,(
    v10_waybel_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_waybel_1_type,type,(
    v2_waybel_1: $i > $o )).

thf(t15_waybel_7,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
     => ( ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
      <=> ! [C: $i] :
            ( ( ( v1_finset_1 @ C )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
           => ( ( r1_tarski @ C @ B )
             => ( r2_hidden @ ( k8_setfam_1 @ A @ C ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ~ ( v1_xboole_0 @ B )
          & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
       => ( ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
        <=> ! [C: $i] :
              ( ( ( v1_finset_1 @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
             => ( ( r1_tarski @ C @ B )
               => ( r2_hidden @ ( k8_setfam_1 @ A @ C ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_waybel_7])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v1_finset_1 @ sk_C_1 )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_finset_1 @ sk_C_1 )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v1_finset_1 @ sk_C_1 )
   <= ( v1_finset_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X35: $i] :
      ( ~ ( v1_finset_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
      | ~ ( r1_tarski @ X35 @ sk_B )
      | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('18',plain,
    ( ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ sk_B )
      | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
      | ~ ( v1_finset_1 @ sk_C_1 ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      & ! [X35: $i] :
          ( ~ ( v1_finset_1 @ X35 )
          | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
          | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
          | ~ ( r1_tarski @ X35 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( ~ ( v1_finset_1 @ sk_C_1 )
      | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      & ! [X35: $i] :
          ( ~ ( v1_finset_1 @ X35 )
          | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
          | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
          | ~ ( r1_tarski @ X35 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      & ( v1_finset_1 @ sk_C_1 )
      & ! [X35: $i] :
          ( ~ ( v1_finset_1 @ X35 )
          | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
          | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
          | ~ ( r1_tarski @ X35 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ~ ! [X35: $i] :
          ( ~ ( v1_finset_1 @ X35 )
          | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
          | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
          | ~ ( r1_tarski @ X35 @ sk_B ) )
    | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
    | ~ ( v1_finset_1 @ sk_C_1 )
    | ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('31',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('34',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(t43_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( ( v1_finset_1 @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) )
               => ( ( C != k1_xboole_0 )
                 => ( r2_hidden @ ( k2_yellow_0 @ A @ C ) @ B ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ( v2_waybel_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t43_waybel_0])).

thf('38',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('39',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('40',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X28 @ X29 ) @ ( k9_setfam_1 @ X28 ) )
      | ( v2_waybel_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ~ ( v3_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_yellow_1 @ X0 ) ) @ ( k9_setfam_1 @ X1 ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf(fc7_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ~ ( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X11: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('43',plain,(
    ! [X12: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('44',plain,(
    ! [X13: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf(dt_k3_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

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

thf('46',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v11_waybel_1 @ X2 )
      | ( v2_lattice3 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc8_waybel_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc1_waybel_7,axiom,(
    ! [A: $i] :
      ( ( v11_waybel_1 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X8: $i] :
      ( v11_waybel_1 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_waybel_7])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ X1 @ ( k3_yellow_1 @ X0 ) ) @ ( k9_setfam_1 @ X1 ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_B ) )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','53'])).

thf('55',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_B ) )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('60',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_A ) )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','62'])).

thf('64',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('66',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('69',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('70',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( ( k6_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
      = ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X4 @ X3 )
        = ( k6_setfam_1 @ X4 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('75',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('76',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('77',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X4 @ X3 )
        = ( k6_setfam_1 @ X4 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( ( k8_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
      = ( k6_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) )
    | ( ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('80',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('81',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( sk_C @ X28 @ X29 )
       != k1_xboole_0 )
      | ( v2_waybel_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t43_waybel_0])).

thf('82',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('83',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( sk_C @ X28 @ X29 )
       != k1_xboole_0 )
      | ( v2_waybel_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ~ ( v3_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( ( sk_C @ X1 @ ( k3_yellow_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X11: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('86',plain,(
    ! [X12: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('87',plain,(
    ! [X13: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('89',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( ( sk_C @ X1 @ ( k3_yellow_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) )
     != k1_xboole_0 )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','90'])).

thf('92',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) )
     != k1_xboole_0 )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k8_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
      = ( k6_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['78','95'])).

thf('97',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('98',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('99',plain,
    ( ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('100',plain,
    ( ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ sk_B )
      | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( v1_finset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B )
      | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( ( r2_hidden @ ( k8_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
      | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('104',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('105',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_finset_1 @ ( sk_C @ X28 @ X29 ) )
      | ( v2_waybel_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t43_waybel_0])).

thf('106',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('107',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_finset_1 @ ( sk_C @ X28 @ X29 ) )
      | ( v2_waybel_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ~ ( v3_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_finset_1 @ ( sk_C @ X1 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X11: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('110',plain,(
    ! [X12: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('111',plain,(
    ! [X13: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('113',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_finset_1 @ ( sk_C @ X1 @ ( k3_yellow_1 @ X0 ) ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112','113'])).

thf('115',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( v1_finset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_finset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( v1_finset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(clc,[status(thm)],['102','119'])).

thf('121',plain,
    ( ( ( r2_hidden @ ( k6_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B )
      | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['96','120'])).

thf('122',plain,
    ( ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ( r2_hidden @ ( k6_setfam_1 @ sk_A @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( r2_hidden @ ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B )
      | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','122'])).

thf('124',plain,
    ( ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf(t20_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
     => ( ( k2_yellow_0 @ ( k3_yellow_1 @ A ) @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('126',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_yellow_0 @ ( k3_yellow_1 @ X22 ) @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t20_yellow_1])).

thf('127',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('128',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('129',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_yellow_0 @ ( k3_yellow_1 @ X22 ) @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X22 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
    | ( ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
      = ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['125','129'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('131',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_xboole_0 @ X33 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( X33 = X34 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('132',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
      | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('135',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('136',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('137',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('138',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['134','139'])).

thf('141',plain,
    ( ( ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) )
      = ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['130','140'])).

thf('142',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('143',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ X29 @ ( sk_C @ X28 @ X29 ) ) @ X28 )
      | ( v2_waybel_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t43_waybel_0])).

thf('144',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('145',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ X29 @ ( sk_C @ X28 @ X29 ) ) @ X28 )
      | ( v2_waybel_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ~ ( v3_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ X0 ) @ ( sk_C @ X1 @ ( k3_yellow_1 @ X0 ) ) ) @ X1 )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X11: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('148',plain,(
    ! [X12: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('149',plain,(
    ! [X13: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('151',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ X0 ) @ ( sk_C @ X1 @ ( k3_yellow_1 @ X0 ) ) ) @ X1 )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151'])).

thf('153',plain,
    ( ~ ( r2_hidden @ ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','152'])).

thf('154',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('156',plain,
    ( ~ ( r2_hidden @ ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ~ ( r2_hidden @ ( k1_setfam_1 @ ( sk_C @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ) @ sk_B )
    | ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','159'])).

thf('161',plain,
    ( ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
   <= ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('162',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ! [X35: $i] :
          ( ~ ( v1_finset_1 @ X35 )
          | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
          | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
          | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ! [X35: $i] :
        ( ~ ( v1_finset_1 @ X35 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
        | ( r2_hidden @ ( k8_setfam_1 @ sk_A @ X35 ) @ sk_B )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('164',plain,
    ( ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('165',plain,(
    ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','23','162','163','164'])).

thf('166',plain,(
    ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','165'])).

thf('167',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('168',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_yellow_0 @ ( k3_yellow_1 @ X22 ) @ X21 )
        = ( k1_setfam_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X22 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('169',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ sk_C_1 )
        = ( k1_setfam_1 @ sk_C_1 ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','164','7','23','162','163','5'])).

thf('171',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('173',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('174',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['164','5','7','23','162','163','3'])).

thf('176',plain,(
    m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['174','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('178',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('179',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_waybel_0 @ X28 @ X29 )
      | ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ X29 @ X30 ) @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( v1_finset_1 @ X30 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t43_waybel_0])).

thf('180',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('181',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('182',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v13_waybel_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_waybel_0 @ X28 @ X29 )
      | ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ X29 @ X30 ) @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k9_setfam_1 @ X28 ) )
      | ~ ( v1_finset_1 @ X30 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v2_lattice3 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ~ ( v3_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_finset_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X1 ) )
      | ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ X0 ) @ X2 ) @ X1 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['178','182'])).

thf('184',plain,(
    ! [X11: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('185',plain,(
    ! [X12: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('186',plain,(
    ! [X13: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('187',plain,(
    ! [X0: $i] :
      ( v2_lattice3 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('188',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ~ ( v1_finset_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k9_setfam_1 @ X1 ) )
      | ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ X0 ) @ X2 ) @ X1 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['183','184','185','186','187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','189'])).

thf('191',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
   <= ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('194',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','164','5','7','23','162','163'])).

thf('195',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['192','195'])).

thf('197',plain,
    ( ~ ( v1_finset_1 @ sk_C_1 )
    | ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['176','196'])).

thf('198',plain,
    ( ( v1_finset_1 @ sk_C_1 )
   <= ( v1_finset_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('199',plain,(
    v1_finset_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['3','164','5','23','162','163','7'])).

thf('200',plain,(
    v1_finset_1 @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ sk_C_1 ) @ sk_B )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['197','200'])).

thf('202',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k2_yellow_0 @ ( k3_yellow_1 @ sk_A ) @ sk_C_1 ) @ sk_B ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( r2_hidden @ ( k1_setfam_1 @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['171','203'])).

thf('205',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('206',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X4 @ X3 )
        = ( k6_setfam_1 @ X4 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('207',plain,
    ( ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
        = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('209',plain,
    ( ( ~ ( r2_hidden @ ( k6_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('211',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('212',plain,
    ( ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ~ ( r2_hidden @ ( k1_setfam_1 @ sk_C_1 ) @ sk_B )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['209','212'])).

thf('214',plain,(
    ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','23','162','163','164'])).

thf('215',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','164','7','23','162','163','5'])).

thf('216',plain,
    ( ~ ( r2_hidden @ ( k1_setfam_1 @ sk_C_1 ) @ sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['204','216'])).

thf('218',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('219',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    ~ ( r2_hidden @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['166','219'])).

thf('221',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('222',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','164','7','23','162','163','5'])).

thf('223',plain,(
    m1_subset_1 @ sk_C_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['221','222'])).

thf('224',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['217','218'])).

thf('225',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X4 @ X3 )
        = X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('227',plain,(
    ! [X4: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ( ( k8_setfam_1 @ X4 @ k1_xboole_0 )
        = X4 ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('229',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('230',plain,(
    ! [X4: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X4 ) ) )
      | ( ( k8_setfam_1 @ X4 @ k1_xboole_0 )
        = X4 ) ) ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference('sup-',[status(thm)],['225','230'])).

thf('232',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
   <= ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('233',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('234',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) )
      = ( k9_setfam_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf(t22_waybel_4,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( r2_hidden @ ( k4_yellow_0 @ A ) @ B ) ) ) )).

thf('235',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ X24 )
      | ~ ( v13_waybel_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r2_hidden @ ( k4_yellow_0 @ X24 ) @ X23 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v2_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t22_waybel_4])).

thf('236',plain,(
    ! [X16: $i] :
      ( ( k9_setfam_1 @ X16 )
      = ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('237',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ X24 )
      | ~ ( v13_waybel_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r2_hidden @ ( k4_yellow_0 @ X24 ) @ X23 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v2_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( r2_hidden @ ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) ) @ X1 )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['234','237'])).

thf('239',plain,(
    ! [X11: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('240',plain,(
    ! [X12: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('241',plain,(
    ! [X13: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('242',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf(cc7_waybel_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v9_waybel_1 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v2_yellow_0 @ A ) ) ) ) )).

thf('243',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v9_waybel_1 @ X1 )
      | ( v2_yellow_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc7_waybel_1])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( v2_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v9_waybel_1 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf(cc10_waybel_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v11_waybel_1 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v9_waybel_1 @ A ) ) ) ) )).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v11_waybel_1 @ X0 )
      | ( v9_waybel_1 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc10_waybel_1])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( v9_waybel_1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v11_waybel_1 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X8: $i] :
      ( v11_waybel_1 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_waybel_7])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( v9_waybel_1 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X9: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('251',plain,(
    ! [X0: $i] :
      ( v9_waybel_1 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v2_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['244','251'])).

thf('253',plain,(
    ! [X9: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('254',plain,(
    ! [X0: $i] :
      ( v2_yellow_0 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf(t19_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf('256',plain,(
    ! [X17: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t19_yellow_1])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v13_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v2_waybel_0 @ X1 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['238','239','240','241','254','255','256'])).

thf('258',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['233','257'])).

thf('259',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['232','260'])).

thf('262',plain,(
    ! [X9: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('263',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','164','5','7','23','162','163'])).

thf('267',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['265','266'])).

thf('268',plain,(
    $false ),
    inference(demod,[status(thm)],['220','231','267'])).


%------------------------------------------------------------------------------
