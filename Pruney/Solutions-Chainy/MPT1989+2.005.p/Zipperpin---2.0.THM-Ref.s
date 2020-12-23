%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BtvpDRvu4t

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:18 EST 2020

% Result     : Theorem 36.37s
% Output     : Refutation 36.37s
% Verified   : 
% Statistics : Number of formulae       :  250 ( 765 expanded)
%              Number of leaves         :   52 ( 240 expanded)
%              Depth                    :   31
%              Number of atoms          : 2521 (11232 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_waybel_6_type,type,(
    v5_waybel_6: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_waybel_7_type,type,(
    v4_waybel_7: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(t38_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
           => ( v4_waybel_7 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v5_waybel_6 @ B @ A )
             => ( v4_waybel_7 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_waybel_7])).

thf('0',plain,(
    ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ~ ( v2_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('9',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','11'])).

thf(d6_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v4_waybel_7 @ B @ A )
          <=> ? [C: $i] :
                ( ( B
                  = ( k1_yellow_0 @ A @ C ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                & ( v1_waybel_7 @ C @ A )
                & ( v12_waybel_0 @ C @ A )
                & ( v1_waybel_0 @ C @ A )
                & ~ ( v1_xboole_0 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( u1_struct_0 @ X48 ) )
      | ( X47
       != ( k1_yellow_0 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v1_waybel_7 @ X49 @ X48 )
      | ~ ( v12_waybel_0 @ X49 @ X48 )
      | ~ ( v1_waybel_0 @ X49 @ X48 )
      | ( v1_xboole_0 @ X49 )
      | ( v4_waybel_7 @ X47 @ X48 )
      | ~ ( l1_orders_2 @ X48 )
      | ~ ( v2_lattice3 @ X48 )
      | ~ ( v1_lattice3 @ X48 )
      | ~ ( v5_orders_2 @ X48 )
      | ~ ( v4_orders_2 @ X48 )
      | ~ ( v3_orders_2 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('14',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v3_orders_2 @ X48 )
      | ~ ( v4_orders_2 @ X48 )
      | ~ ( v5_orders_2 @ X48 )
      | ~ ( v1_lattice3 @ X48 )
      | ~ ( v2_lattice3 @ X48 )
      | ~ ( l1_orders_2 @ X48 )
      | ( v4_waybel_7 @ ( k1_yellow_0 @ X48 @ X49 ) @ X48 )
      | ( v1_xboole_0 @ X49 )
      | ~ ( v1_waybel_0 @ X49 @ X48 )
      | ~ ( v12_waybel_0 @ X49 @ X48 )
      | ~ ( v1_waybel_7 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X48 @ X49 ) @ ( u1_struct_0 @ X48 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc12_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) )).

thf('17',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( v12_waybel_0 @ ( k5_waybel_0 @ X36 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc12_waybel_0])).

thf('18',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc8_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ A @ B ) )
        & ( v1_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ( v1_waybel_0 @ ( k5_waybel_0 @ X38 @ X39 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('26',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('31',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','23','31','32','33','34','35','36','37'])).

thf('39',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_xboole_0 @ ( k5_waybel_0 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['41','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
           => ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) )).

thf('52',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( u1_struct_0 @ X51 ) )
      | ( v1_waybel_7 @ ( k5_waybel_0 @ X51 @ X50 ) @ X51 )
      | ~ ( v5_waybel_6 @ X50 @ X51 )
      | ~ ( l1_orders_2 @ X51 )
      | ~ ( v2_lattice3 @ X51 )
      | ~ ( v1_lattice3 @ X51 )
      | ~ ( v5_orders_2 @ X51 )
      | ~ ( v4_orders_2 @ X51 )
      | ~ ( v3_orders_2 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t37_waybel_7])).

thf('53',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_6 @ sk_B @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_waybel_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','60'])).

thf('62',plain,(
    v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['50','61'])).

thf(t30_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) )
               => ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ B @ D ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_lattice3 @ X21 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('64',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_1 @ X22 @ X23 @ X24 @ X25 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('68',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) )
              <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r1_orders_2 @ X41 @ X42 @ X40 )
      | ( r2_hidden @ X42 @ ( k5_waybel_0 @ X41 @ X40 ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( l1_orders_2 @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ sk_B )
    | ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf(l28_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k11_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ D @ B )
                      & ( r1_orders_2 @ A @ D @ C )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ E @ B )
                              & ( r1_orders_2 @ A @ E @ C ) )
                           => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k11_lattice3 @ X12 @ X11 @ X14 ) )
      | ( r1_orders_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('81',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ ( k11_lattice3 @ X12 @ X11 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X12 @ X11 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('90',plain,(
    r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('93',plain,(
    r2_hidden @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('95',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_1 @ X22 @ X23 @ X24 @ X25 )
      | ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_orders_2 @ X5 @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_1 @ X1 @ X5 @ X4 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ X0 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ X0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ X2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['93','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_orders_2 @ X12 @ X13 @ X11 )
      | ~ ( r1_orders_2 @ X12 @ X13 @ X14 )
      | ( r1_orders_2 @ X12 @ ( sk_E @ X13 @ X14 @ X11 @ X12 ) @ X11 )
      | ( X13
        = ( k11_lattice3 @ X12 @ X11 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_B @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_B @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','112'])).

thf('114',plain,(
    r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['88','89'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_waybel_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ~ ( ( r1_orders_2 @ A @ ( k11_lattice3 @ A @ C @ D ) @ B )
                        & ~ ( r1_orders_2 @ A @ C @ B )
                        & ~ ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) )).

thf('116',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X44 ) )
      | ~ ( v5_waybel_6 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X44 ) )
      | ~ ( r1_orders_2 @ X44 @ ( k11_lattice3 @ X44 @ X46 @ X45 ) @ X43 )
      | ( r1_orders_2 @ X44 @ X45 @ X43 )
      | ( r1_orders_2 @ X44 @ X46 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X44 ) )
      | ~ ( l1_orders_2 @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_6])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ X0 @ X1 ) @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_waybel_6 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v5_waybel_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ X0 @ X1 ) @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('127',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('130',plain,
    ( ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_B @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_orders_2 @ X12 @ X13 @ X11 )
      | ~ ( r1_orders_2 @ X12 @ X13 @ X14 )
      | ~ ( r1_orders_2 @ X12 @ ( sk_E @ X13 @ X14 @ X11 @ X12 ) @ X13 )
      | ( X13
        = ( k11_lattice3 @ X12 @ X11 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,
    ( ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['125','126'])).

thf('141',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['125','126'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
    | ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('146',plain,
    ( sk_B
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X2 @ X1 @ X0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X2 )
      | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X2 ) ) ),
    inference(demod,[status(thm)],['101','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X3 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 ) ) ),
    inference(condensation,[status(thm)],['148'])).

thf('150',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('151',plain,(
    ! [X29: $i,X30: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r2_lattice3 @ X30 @ X33 @ X29 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X33 @ X29 @ X30 ) @ X33 @ X29 @ X30 )
      | ( zip_tseitin_2 @ X33 @ X29 @ X30 )
      | ~ ( l1_orders_2 @ X30 )
      | ~ ( v5_orders_2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['149','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r2_hidden @ X42 @ ( k5_waybel_0 @ X41 @ X40 ) )
      | ( r1_orders_2 @ X41 @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( l1_orders_2 @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','171'])).

thf('173',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['161','172'])).

thf('174',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ ( sk_D @ X4 @ X6 @ X5 ) @ X4 )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['174','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('182',plain,(
    r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['156','182'])).

thf('184',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ~ ( r1_orders_2 @ X21 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_1 @ X22 @ X23 @ X24 @ X25 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('189',plain,
    ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['180','181'])).

thf('191',plain,
    ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X28
        = ( k1_yellow_0 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_2 @ X27 @ X28 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('194',plain,
    ( sk_B
    = ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v4_waybel_7 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['62','194'])).

thf('196',plain,(
    $false ),
    inference(demod,[status(thm)],['0','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BtvpDRvu4t
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 36.37/36.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 36.37/36.57  % Solved by: fo/fo7.sh
% 36.37/36.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.37/36.57  % done 6274 iterations in 36.104s
% 36.37/36.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 36.37/36.57  % SZS output start Refutation
% 36.37/36.57  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 36.37/36.57  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 36.37/36.57  thf(sk_B_type, type, sk_B: $i).
% 36.37/36.57  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 36.37/36.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 36.37/36.57  thf(v5_waybel_6_type, type, v5_waybel_6: $i > $i > $o).
% 36.37/36.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 36.37/36.57  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 36.37/36.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 36.37/36.57  thf(v12_waybel_0_type, type, v12_waybel_0: $i > $i > $o).
% 36.37/36.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 36.37/36.57  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 36.37/36.57  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 36.37/36.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 36.37/36.57  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 36.37/36.57  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 36.37/36.57  thf(sk_A_type, type, sk_A: $i).
% 36.37/36.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 36.37/36.57  thf(v1_waybel_7_type, type, v1_waybel_7: $i > $i > $o).
% 36.37/36.57  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 36.37/36.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 36.37/36.57  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 36.37/36.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 36.37/36.57  thf(v4_waybel_7_type, type, v4_waybel_7: $i > $i > $o).
% 36.37/36.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 36.37/36.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 36.37/36.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 36.37/36.57  thf(v1_waybel_0_type, type, v1_waybel_0: $i > $i > $o).
% 36.37/36.57  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 36.37/36.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 36.37/36.57  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 36.37/36.57  thf(t38_waybel_7, conjecture,
% 36.37/36.57    (![A:$i]:
% 36.37/36.57     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 36.37/36.57         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 36.37/36.57       ( ![B:$i]:
% 36.37/36.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57           ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ))).
% 36.37/36.57  thf(zf_stmt_0, negated_conjecture,
% 36.37/36.57    (~( ![A:$i]:
% 36.37/36.57        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 36.37/36.57            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 36.37/36.57          ( ![B:$i]:
% 36.37/36.57            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57              ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ) )),
% 36.37/36.57    inference('cnf.neg', [status(esa)], [t38_waybel_7])).
% 36.37/36.57  thf('0', plain, (~ (v4_waybel_7 @ sk_B @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf(dt_k1_yellow_0, axiom,
% 36.37/36.57    (![A:$i,B:$i]:
% 36.37/36.57     ( ( l1_orders_2 @ A ) =>
% 36.37/36.57       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 36.37/36.57  thf('1', plain,
% 36.37/36.57      (![X16 : $i, X17 : $i]:
% 36.37/36.57         (~ (l1_orders_2 @ X16)
% 36.37/36.57          | (m1_subset_1 @ (k1_yellow_0 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 36.37/36.57      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 36.37/36.57  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf(dt_k5_waybel_0, axiom,
% 36.37/36.57    (![A:$i,B:$i]:
% 36.37/36.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 36.37/36.57         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 36.37/36.57       ( m1_subset_1 @
% 36.37/36.57         ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 36.37/36.57  thf('3', plain,
% 36.37/36.57      (![X34 : $i, X35 : $i]:
% 36.37/36.57         (~ (l1_orders_2 @ X34)
% 36.37/36.57          | (v2_struct_0 @ X34)
% 36.37/36.57          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 36.37/36.57          | (m1_subset_1 @ (k5_waybel_0 @ X34 @ X35) @ 
% 36.37/36.57             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 36.37/36.57      inference('cnf', [status(esa)], [dt_k5_waybel_0])).
% 36.37/36.57  thf('4', plain,
% 36.37/36.57      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 36.37/36.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.37/36.57        | (v2_struct_0 @ sk_A)
% 36.37/36.57        | ~ (l1_orders_2 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['2', '3'])).
% 36.37/36.57  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('6', plain,
% 36.37/36.57      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 36.37/36.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.37/36.57        | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('demod', [status(thm)], ['4', '5'])).
% 36.37/36.57  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf(cc2_lattice3, axiom,
% 36.37/36.57    (![A:$i]:
% 36.37/36.57     ( ( l1_orders_2 @ A ) =>
% 36.37/36.57       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 36.37/36.57  thf('8', plain,
% 36.37/36.57      (![X3 : $i]:
% 36.37/36.57         (~ (v2_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 36.37/36.57      inference('cnf', [status(esa)], [cc2_lattice3])).
% 36.37/36.57  thf('9', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v2_lattice3 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['7', '8'])).
% 36.37/36.57  thf('10', plain, ((v2_lattice3 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.57      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.57  thf('12', plain,
% 36.37/36.57      ((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 36.37/36.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.37/36.57      inference('clc', [status(thm)], ['6', '11'])).
% 36.37/36.57  thf(d6_waybel_7, axiom,
% 36.37/36.57    (![A:$i]:
% 36.37/36.57     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 36.37/36.57         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 36.37/36.57       ( ![B:$i]:
% 36.37/36.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57           ( ( v4_waybel_7 @ B @ A ) <=>
% 36.37/36.57             ( ?[C:$i]:
% 36.37/36.57               ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 36.37/36.57                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 36.37/36.57                 ( v1_waybel_7 @ C @ A ) & ( v12_waybel_0 @ C @ A ) & 
% 36.37/36.57                 ( v1_waybel_0 @ C @ A ) & ( ~( v1_xboole_0 @ C ) ) ) ) ) ) ) ))).
% 36.37/36.57  thf('13', plain,
% 36.37/36.57      (![X47 : $i, X48 : $i, X49 : $i]:
% 36.37/36.57         (~ (m1_subset_1 @ X47 @ (u1_struct_0 @ X48))
% 36.37/36.57          | ((X47) != (k1_yellow_0 @ X48 @ X49))
% 36.37/36.57          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 36.37/36.57          | ~ (v1_waybel_7 @ X49 @ X48)
% 36.37/36.57          | ~ (v12_waybel_0 @ X49 @ X48)
% 36.37/36.57          | ~ (v1_waybel_0 @ X49 @ X48)
% 36.37/36.57          | (v1_xboole_0 @ X49)
% 36.37/36.57          | (v4_waybel_7 @ X47 @ X48)
% 36.37/36.57          | ~ (l1_orders_2 @ X48)
% 36.37/36.57          | ~ (v2_lattice3 @ X48)
% 36.37/36.57          | ~ (v1_lattice3 @ X48)
% 36.37/36.57          | ~ (v5_orders_2 @ X48)
% 36.37/36.57          | ~ (v4_orders_2 @ X48)
% 36.37/36.57          | ~ (v3_orders_2 @ X48))),
% 36.37/36.57      inference('cnf', [status(esa)], [d6_waybel_7])).
% 36.37/36.57  thf('14', plain,
% 36.37/36.57      (![X48 : $i, X49 : $i]:
% 36.37/36.57         (~ (v3_orders_2 @ X48)
% 36.37/36.57          | ~ (v4_orders_2 @ X48)
% 36.37/36.57          | ~ (v5_orders_2 @ X48)
% 36.37/36.57          | ~ (v1_lattice3 @ X48)
% 36.37/36.57          | ~ (v2_lattice3 @ X48)
% 36.37/36.57          | ~ (l1_orders_2 @ X48)
% 36.37/36.57          | (v4_waybel_7 @ (k1_yellow_0 @ X48 @ X49) @ X48)
% 36.37/36.57          | (v1_xboole_0 @ X49)
% 36.37/36.57          | ~ (v1_waybel_0 @ X49 @ X48)
% 36.37/36.57          | ~ (v12_waybel_0 @ X49 @ X48)
% 36.37/36.57          | ~ (v1_waybel_7 @ X49 @ X48)
% 36.37/36.57          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 36.37/36.57          | ~ (m1_subset_1 @ (k1_yellow_0 @ X48 @ X49) @ (u1_struct_0 @ X48)))),
% 36.37/36.57      inference('simplify', [status(thm)], ['13'])).
% 36.37/36.57  thf('15', plain,
% 36.37/36.57      ((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 36.37/36.57           (u1_struct_0 @ sk_A))
% 36.37/36.57        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | ~ (v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | ~ (v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 36.37/36.57           sk_A)
% 36.37/36.57        | ~ (l1_orders_2 @ sk_A)
% 36.37/36.57        | ~ (v2_lattice3 @ sk_A)
% 36.37/36.57        | ~ (v1_lattice3 @ sk_A)
% 36.37/36.57        | ~ (v5_orders_2 @ sk_A)
% 36.37/36.57        | ~ (v4_orders_2 @ sk_A)
% 36.37/36.57        | ~ (v3_orders_2 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['12', '14'])).
% 36.37/36.57  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf(fc12_waybel_0, axiom,
% 36.37/36.57    (![A:$i,B:$i]:
% 36.37/36.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_orders_2 @ A ) & 
% 36.37/36.57         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 36.37/36.57       ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ))).
% 36.37/36.57  thf('17', plain,
% 36.37/36.57      (![X36 : $i, X37 : $i]:
% 36.37/36.57         (~ (l1_orders_2 @ X36)
% 36.37/36.57          | ~ (v4_orders_2 @ X36)
% 36.37/36.57          | (v2_struct_0 @ X36)
% 36.37/36.57          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 36.37/36.57          | (v12_waybel_0 @ (k5_waybel_0 @ X36 @ X37) @ X36))),
% 36.37/36.57      inference('cnf', [status(esa)], [fc12_waybel_0])).
% 36.37/36.57  thf('18', plain,
% 36.37/36.57      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | (v2_struct_0 @ sk_A)
% 36.37/36.57        | ~ (v4_orders_2 @ sk_A)
% 36.37/36.57        | ~ (l1_orders_2 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['16', '17'])).
% 36.37/36.57  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('21', plain,
% 36.37/36.57      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('demod', [status(thm)], ['18', '19', '20'])).
% 36.37/36.57  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.57      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.57  thf('23', plain, ((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 36.37/36.57      inference('clc', [status(thm)], ['21', '22'])).
% 36.37/36.57  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf(fc8_waybel_0, axiom,
% 36.37/36.57    (![A:$i,B:$i]:
% 36.37/36.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 36.37/36.57         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 36.37/36.57       ( ( ~( v1_xboole_0 @ ( k5_waybel_0 @ A @ B ) ) ) & 
% 36.37/36.57         ( v1_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ))).
% 36.37/36.57  thf('25', plain,
% 36.37/36.57      (![X38 : $i, X39 : $i]:
% 36.37/36.57         (~ (l1_orders_2 @ X38)
% 36.37/36.57          | ~ (v3_orders_2 @ X38)
% 36.37/36.57          | (v2_struct_0 @ X38)
% 36.37/36.57          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 36.37/36.57          | (v1_waybel_0 @ (k5_waybel_0 @ X38 @ X39) @ X38))),
% 36.37/36.57      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 36.37/36.57  thf('26', plain,
% 36.37/36.57      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | (v2_struct_0 @ sk_A)
% 36.37/36.57        | ~ (v3_orders_2 @ sk_A)
% 36.37/36.57        | ~ (l1_orders_2 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['24', '25'])).
% 36.37/36.57  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('29', plain,
% 36.37/36.57      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('demod', [status(thm)], ['26', '27', '28'])).
% 36.37/36.57  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.57      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.57  thf('31', plain, ((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 36.37/36.57      inference('clc', [status(thm)], ['29', '30'])).
% 36.37/36.57  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('33', plain, ((v2_lattice3 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('34', plain, ((v1_lattice3 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('35', plain, ((v5_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('36', plain, ((v4_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('37', plain, ((v3_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('38', plain,
% 36.37/36.57      ((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 36.37/36.57           (u1_struct_0 @ sk_A))
% 36.37/36.57        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 36.37/36.57           sk_A))),
% 36.37/36.57      inference('demod', [status(thm)],
% 36.37/36.57                ['15', '23', '31', '32', '33', '34', '35', '36', '37'])).
% 36.37/36.57  thf('39', plain,
% 36.37/36.57      ((~ (l1_orders_2 @ sk_A)
% 36.37/36.57        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 36.37/36.57           sk_A)
% 36.37/36.57        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['1', '38'])).
% 36.37/36.57  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('41', plain,
% 36.37/36.57      (((v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 36.37/36.57         sk_A)
% 36.37/36.57        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 36.37/36.57      inference('demod', [status(thm)], ['39', '40'])).
% 36.37/36.57  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('43', plain,
% 36.37/36.57      (![X38 : $i, X39 : $i]:
% 36.37/36.57         (~ (l1_orders_2 @ X38)
% 36.37/36.57          | ~ (v3_orders_2 @ X38)
% 36.37/36.57          | (v2_struct_0 @ X38)
% 36.37/36.57          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 36.37/36.57          | ~ (v1_xboole_0 @ (k5_waybel_0 @ X38 @ X39)))),
% 36.37/36.57      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 36.37/36.57  thf('44', plain,
% 36.37/36.57      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57        | (v2_struct_0 @ sk_A)
% 36.37/36.57        | ~ (v3_orders_2 @ sk_A)
% 36.37/36.57        | ~ (l1_orders_2 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['42', '43'])).
% 36.37/36.57  thf('45', plain, ((v3_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('46', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('47', plain,
% 36.37/36.57      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('demod', [status(thm)], ['44', '45', '46'])).
% 36.37/36.57  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.57      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.57  thf('49', plain, (~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))),
% 36.37/36.57      inference('clc', [status(thm)], ['47', '48'])).
% 36.37/36.57  thf('50', plain,
% 36.37/36.57      ((~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 36.37/36.57        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 36.37/36.57           sk_A))),
% 36.37/36.57      inference('clc', [status(thm)], ['41', '49'])).
% 36.37/36.57  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf(t37_waybel_7, axiom,
% 36.37/36.57    (![A:$i]:
% 36.37/36.57     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 36.37/36.57         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 36.37/36.57       ( ![B:$i]:
% 36.37/36.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57           ( ( v5_waybel_6 @ B @ A ) =>
% 36.37/36.57             ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 36.37/36.57  thf('52', plain,
% 36.37/36.57      (![X50 : $i, X51 : $i]:
% 36.37/36.57         (~ (m1_subset_1 @ X50 @ (u1_struct_0 @ X51))
% 36.37/36.57          | (v1_waybel_7 @ (k5_waybel_0 @ X51 @ X50) @ X51)
% 36.37/36.57          | ~ (v5_waybel_6 @ X50 @ X51)
% 36.37/36.57          | ~ (l1_orders_2 @ X51)
% 36.37/36.57          | ~ (v2_lattice3 @ X51)
% 36.37/36.57          | ~ (v1_lattice3 @ X51)
% 36.37/36.57          | ~ (v5_orders_2 @ X51)
% 36.37/36.57          | ~ (v4_orders_2 @ X51)
% 36.37/36.57          | ~ (v3_orders_2 @ X51))),
% 36.37/36.57      inference('cnf', [status(esa)], [t37_waybel_7])).
% 36.37/36.57  thf('53', plain,
% 36.37/36.57      ((~ (v3_orders_2 @ sk_A)
% 36.37/36.57        | ~ (v4_orders_2 @ sk_A)
% 36.37/36.57        | ~ (v5_orders_2 @ sk_A)
% 36.37/36.57        | ~ (v1_lattice3 @ sk_A)
% 36.37/36.57        | ~ (v2_lattice3 @ sk_A)
% 36.37/36.57        | ~ (l1_orders_2 @ sk_A)
% 36.37/36.57        | ~ (v5_waybel_6 @ sk_B @ sk_A)
% 36.37/36.57        | (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['51', '52'])).
% 36.37/36.57  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('55', plain, ((v4_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('56', plain, ((v5_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('57', plain, ((v1_lattice3 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('58', plain, ((v2_lattice3 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('60', plain, ((v5_waybel_6 @ sk_B @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('61', plain, ((v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 36.37/36.57      inference('demod', [status(thm)],
% 36.37/36.57                ['53', '54', '55', '56', '57', '58', '59', '60'])).
% 36.37/36.57  thf('62', plain,
% 36.37/36.57      ((v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ sk_A)),
% 36.37/36.57      inference('demod', [status(thm)], ['50', '61'])).
% 36.37/36.57  thf(t30_yellow_0, axiom,
% 36.37/36.57    (![A:$i]:
% 36.37/36.57     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 36.37/36.57       ( ![B:$i]:
% 36.37/36.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57           ( ![C:$i]:
% 36.37/36.57             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 36.37/36.57                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 36.37/36.57                 ( ( ![D:$i]:
% 36.37/36.57                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 36.37/36.57                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 36.37/36.57                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 36.37/36.57               ( ( ( ![D:$i]:
% 36.37/36.57                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 36.37/36.57                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 36.37/36.57                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 36.37/36.57                 ( ( r1_yellow_0 @ A @ C ) & 
% 36.37/36.57                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 36.37/36.57  thf(zf_stmt_1, axiom,
% 36.37/36.57    (![D:$i,C:$i,B:$i,A:$i]:
% 36.37/36.57     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 36.37/36.57       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 36.37/36.57  thf('63', plain,
% 36.37/36.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 36.37/36.57         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 36.37/36.57          | (r2_lattice3 @ X21 @ X19 @ X18))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.37/36.57  thf(zf_stmt_2, axiom,
% 36.37/36.57    (![D:$i,C:$i,B:$i,A:$i]:
% 36.37/36.57     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 36.37/36.57       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 36.37/36.57  thf('64', plain,
% 36.37/36.57      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 36.37/36.57         ((zip_tseitin_1 @ X22 @ X23 @ X24 @ X25)
% 36.37/36.57          | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 36.37/36.57  thf('65', plain,
% 36.37/36.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.37/36.57         ((r2_lattice3 @ X0 @ X2 @ X3) | (zip_tseitin_1 @ X3 @ X2 @ X1 @ X0))),
% 36.37/36.57      inference('sup-', [status(thm)], ['63', '64'])).
% 36.37/36.57  thf('66', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('67', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf(dt_k11_lattice3, axiom,
% 36.37/36.57    (![A:$i,B:$i,C:$i]:
% 36.37/36.57     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 36.37/36.57         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 36.37/36.57       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 36.37/36.57  thf('68', plain,
% 36.37/36.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 36.37/36.57         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 36.37/36.57          | ~ (l1_orders_2 @ X9)
% 36.37/36.57          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 36.37/36.57          | (m1_subset_1 @ (k11_lattice3 @ X9 @ X8 @ X10) @ (u1_struct_0 @ X9)))),
% 36.37/36.57      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 36.37/36.57  thf('69', plain,
% 36.37/36.57      (![X0 : $i]:
% 36.37/36.57         ((m1_subset_1 @ (k11_lattice3 @ sk_A @ sk_B @ X0) @ 
% 36.37/36.57           (u1_struct_0 @ sk_A))
% 36.37/36.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.57          | ~ (l1_orders_2 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['67', '68'])).
% 36.37/36.57  thf('70', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('71', plain,
% 36.37/36.57      (![X0 : $i]:
% 36.37/36.57         ((m1_subset_1 @ (k11_lattice3 @ sk_A @ sk_B @ X0) @ 
% 36.37/36.57           (u1_struct_0 @ sk_A))
% 36.37/36.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 36.37/36.57      inference('demod', [status(thm)], ['69', '70'])).
% 36.37/36.57  thf('72', plain,
% 36.37/36.57      ((m1_subset_1 @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ 
% 36.37/36.57        (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['66', '71'])).
% 36.37/36.57  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf(t17_waybel_0, axiom,
% 36.37/36.57    (![A:$i]:
% 36.37/36.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 36.37/36.57       ( ![B:$i]:
% 36.37/36.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57           ( ![C:$i]:
% 36.37/36.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57               ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) ) <=>
% 36.37/36.57                 ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 36.37/36.57  thf('74', plain,
% 36.37/36.57      (![X40 : $i, X41 : $i, X42 : $i]:
% 36.37/36.57         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 36.37/36.57          | ~ (r1_orders_2 @ X41 @ X42 @ X40)
% 36.37/36.57          | (r2_hidden @ X42 @ (k5_waybel_0 @ X41 @ X40))
% 36.37/36.57          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 36.37/36.57          | ~ (l1_orders_2 @ X41)
% 36.37/36.57          | (v2_struct_0 @ X41))),
% 36.37/36.57      inference('cnf', [status(esa)], [t17_waybel_0])).
% 36.37/36.57  thf('75', plain,
% 36.37/36.57      (![X0 : $i]:
% 36.37/36.57         ((v2_struct_0 @ sk_A)
% 36.37/36.57          | ~ (l1_orders_2 @ sk_A)
% 36.37/36.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.57          | (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 36.37/36.57      inference('sup-', [status(thm)], ['73', '74'])).
% 36.37/36.57  thf('76', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('77', plain,
% 36.37/36.57      (![X0 : $i]:
% 36.37/36.57         ((v2_struct_0 @ sk_A)
% 36.37/36.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.57          | (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 36.37/36.57      inference('demod', [status(thm)], ['75', '76'])).
% 36.37/36.57  thf('78', plain,
% 36.37/36.57      ((~ (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ sk_B)
% 36.37/36.57        | (r2_hidden @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ 
% 36.37/36.57           (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57        | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['72', '77'])).
% 36.37/36.57  thf('79', plain,
% 36.37/36.57      ((m1_subset_1 @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ 
% 36.37/36.57        (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['66', '71'])).
% 36.37/36.57  thf(l28_lattice3, axiom,
% 36.37/36.57    (![A:$i]:
% 36.37/36.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 36.37/36.57         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 36.37/36.57       ( ![B:$i]:
% 36.37/36.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57           ( ![C:$i]:
% 36.37/36.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57               ( ![D:$i]:
% 36.37/36.57                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 36.37/36.57                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 36.37/36.57                       ( r1_orders_2 @ A @ D @ C ) & 
% 36.37/36.57                       ( ![E:$i]:
% 36.37/36.57                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 36.37/36.57                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 36.37/36.57                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 36.37/36.57  thf('80', plain,
% 36.37/36.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 36.37/36.57         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 36.37/36.57          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 36.37/36.57          | ((X13) != (k11_lattice3 @ X12 @ X11 @ X14))
% 36.37/36.57          | (r1_orders_2 @ X12 @ X13 @ X14)
% 36.37/36.57          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 36.37/36.57          | ~ (l1_orders_2 @ X12)
% 36.37/36.57          | ~ (v2_lattice3 @ X12)
% 36.37/36.57          | ~ (v5_orders_2 @ X12)
% 36.37/36.57          | (v2_struct_0 @ X12))),
% 36.37/36.57      inference('cnf', [status(esa)], [l28_lattice3])).
% 36.37/36.57  thf('81', plain,
% 36.37/36.57      (![X11 : $i, X12 : $i, X14 : $i]:
% 36.37/36.57         ((v2_struct_0 @ X12)
% 36.37/36.57          | ~ (v5_orders_2 @ X12)
% 36.37/36.57          | ~ (v2_lattice3 @ X12)
% 36.37/36.57          | ~ (l1_orders_2 @ X12)
% 36.37/36.57          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 36.37/36.57          | (r1_orders_2 @ X12 @ (k11_lattice3 @ X12 @ X11 @ X14) @ X14)
% 36.37/36.57          | ~ (m1_subset_1 @ (k11_lattice3 @ X12 @ X11 @ X14) @ 
% 36.37/36.57               (u1_struct_0 @ X12))
% 36.37/36.57          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 36.37/36.57      inference('simplify', [status(thm)], ['80'])).
% 36.37/36.57  thf('82', plain,
% 36.37/36.57      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 36.37/36.57        | (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ sk_B)
% 36.37/36.57        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 36.37/36.57        | ~ (l1_orders_2 @ sk_A)
% 36.37/36.57        | ~ (v2_lattice3 @ sk_A)
% 36.37/36.57        | ~ (v5_orders_2 @ sk_A)
% 36.37/36.57        | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['79', '81'])).
% 36.37/36.57  thf('83', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('86', plain, ((v2_lattice3 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('87', plain, ((v5_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('88', plain,
% 36.37/36.57      (((r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ sk_B)
% 36.37/36.57        | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('demod', [status(thm)], ['82', '83', '84', '85', '86', '87'])).
% 36.37/36.57  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.57      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.57  thf('90', plain,
% 36.37/36.57      ((r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ sk_B)),
% 36.37/36.57      inference('clc', [status(thm)], ['88', '89'])).
% 36.37/36.57  thf('91', plain,
% 36.37/36.57      (((r2_hidden @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ 
% 36.37/36.57         (k5_waybel_0 @ sk_A @ sk_B))
% 36.37/36.57        | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('demod', [status(thm)], ['78', '90'])).
% 36.37/36.57  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.57      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.57  thf('93', plain,
% 36.37/36.57      ((r2_hidden @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ 
% 36.37/36.57        (k5_waybel_0 @ sk_A @ sk_B))),
% 36.37/36.57      inference('clc', [status(thm)], ['91', '92'])).
% 36.37/36.57  thf('94', plain,
% 36.37/36.57      ((m1_subset_1 @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ 
% 36.37/36.57        (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['66', '71'])).
% 36.37/36.57  thf('95', plain,
% 36.37/36.57      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 36.37/36.57         ((zip_tseitin_1 @ X22 @ X23 @ X24 @ X25)
% 36.37/36.57          | (m1_subset_1 @ X22 @ (u1_struct_0 @ X25)))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 36.37/36.57  thf(d9_lattice3, axiom,
% 36.37/36.57    (![A:$i]:
% 36.37/36.57     ( ( l1_orders_2 @ A ) =>
% 36.37/36.57       ( ![B:$i,C:$i]:
% 36.37/36.57         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 36.37/36.57             ( ![D:$i]:
% 36.37/36.57               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.57                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 36.37/36.57  thf('96', plain,
% 36.37/36.57      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 36.37/36.57         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 36.37/36.57          | ~ (r2_lattice3 @ X5 @ X6 @ X4)
% 36.37/36.57          | ~ (r2_hidden @ X7 @ X6)
% 36.37/36.57          | (r1_orders_2 @ X5 @ X7 @ X4)
% 36.37/36.57          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 36.37/36.57          | ~ (l1_orders_2 @ X5))),
% 36.37/36.57      inference('cnf', [status(esa)], [d9_lattice3])).
% 36.37/36.57  thf('97', plain,
% 36.37/36.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 36.37/36.57         ((zip_tseitin_1 @ X1 @ X5 @ X4 @ X0)
% 36.37/36.57          | ~ (l1_orders_2 @ X0)
% 36.37/36.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 36.37/36.57          | (r1_orders_2 @ X0 @ X2 @ X1)
% 36.37/36.57          | ~ (r2_hidden @ X2 @ X3)
% 36.37/36.57          | ~ (r2_lattice3 @ X0 @ X3 @ X1))),
% 36.37/36.57      inference('sup-', [status(thm)], ['95', '96'])).
% 36.37/36.57  thf('98', plain,
% 36.37/36.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.37/36.57         (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 36.37/36.57          | ~ (r2_hidden @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ X1)
% 36.37/36.57          | (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ X0)
% 36.37/36.57          | ~ (l1_orders_2 @ sk_A)
% 36.37/36.57          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['94', '97'])).
% 36.37/36.57  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('100', plain,
% 36.37/36.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.37/36.57         (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 36.37/36.57          | ~ (r2_hidden @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ X1)
% 36.37/36.57          | (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ X0)
% 36.37/36.57          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 36.37/36.57      inference('demod', [status(thm)], ['98', '99'])).
% 36.37/36.57  thf('101', plain,
% 36.37/36.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.37/36.57         ((zip_tseitin_1 @ X2 @ X1 @ X0 @ sk_A)
% 36.37/36.57          | (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ X2)
% 36.37/36.57          | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ X2))),
% 36.37/36.57      inference('sup-', [status(thm)], ['93', '100'])).
% 36.37/36.57  thf('102', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('103', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('104', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('105', plain,
% 36.37/36.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 36.37/36.57         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 36.37/36.57          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 36.37/36.57          | ~ (r1_orders_2 @ X12 @ X13 @ X11)
% 36.37/36.57          | ~ (r1_orders_2 @ X12 @ X13 @ X14)
% 36.37/36.57          | (r1_orders_2 @ X12 @ (sk_E @ X13 @ X14 @ X11 @ X12) @ X11)
% 36.37/36.57          | ((X13) = (k11_lattice3 @ X12 @ X11 @ X14))
% 36.37/36.57          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 36.37/36.57          | ~ (l1_orders_2 @ X12)
% 36.37/36.57          | ~ (v2_lattice3 @ X12)
% 36.37/36.57          | ~ (v5_orders_2 @ X12)
% 36.37/36.57          | (v2_struct_0 @ X12))),
% 36.37/36.57      inference('cnf', [status(esa)], [l28_lattice3])).
% 36.37/36.57  thf('106', plain,
% 36.37/36.57      (![X0 : $i, X1 : $i]:
% 36.37/36.57         ((v2_struct_0 @ sk_A)
% 36.37/36.57          | ~ (v5_orders_2 @ sk_A)
% 36.37/36.57          | ~ (v2_lattice3 @ sk_A)
% 36.37/36.57          | ~ (l1_orders_2 @ sk_A)
% 36.37/36.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.57          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 36.37/36.57          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 36.37/36.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 36.37/36.57      inference('sup-', [status(thm)], ['104', '105'])).
% 36.37/36.57  thf('107', plain, ((v5_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('108', plain, ((v2_lattice3 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('109', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.57  thf('110', plain,
% 36.37/36.57      (![X0 : $i, X1 : $i]:
% 36.37/36.57         ((v2_struct_0 @ sk_A)
% 36.37/36.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.57          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 36.37/36.57          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 36.37/36.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 36.37/36.57      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 36.37/36.57  thf('111', plain,
% 36.37/36.57      (![X0 : $i]:
% 36.37/36.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 36.37/36.57          | (r1_orders_2 @ sk_A @ (sk_E @ X0 @ sk_B @ sk_B @ sk_A) @ sk_B)
% 36.37/36.57          | ((X0) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.57          | (v2_struct_0 @ sk_A))),
% 36.37/36.57      inference('sup-', [status(thm)], ['103', '110'])).
% 36.37/36.57  thf('112', plain,
% 36.37/36.57      (![X0 : $i]:
% 36.37/36.57         ((v2_struct_0 @ sk_A)
% 36.37/36.57          | ((X0) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.57          | (r1_orders_2 @ sk_A @ (sk_E @ X0 @ sk_B @ sk_B @ sk_A) @ sk_B)
% 36.37/36.57          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 36.37/36.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 36.37/36.57      inference('simplify', [status(thm)], ['111'])).
% 36.37/36.58  thf('113', plain,
% 36.37/36.58      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 36.37/36.58        | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_B @ sk_B @ sk_A) @ sk_B)
% 36.37/36.58        | ((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.58        | (v2_struct_0 @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['102', '112'])).
% 36.37/36.58  thf('114', plain,
% 36.37/36.58      ((r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_B) @ sk_B)),
% 36.37/36.58      inference('clc', [status(thm)], ['88', '89'])).
% 36.37/36.58  thf('115', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf(d6_waybel_6, axiom,
% 36.37/36.58    (![A:$i]:
% 36.37/36.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 36.37/36.58       ( ![B:$i]:
% 36.37/36.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.58           ( ( v5_waybel_6 @ B @ A ) <=>
% 36.37/36.58             ( ![C:$i]:
% 36.37/36.58               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.58                 ( ![D:$i]:
% 36.37/36.58                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.58                     ( ~( ( r1_orders_2 @ A @ ( k11_lattice3 @ A @ C @ D ) @ B ) & 
% 36.37/36.58                          ( ~( r1_orders_2 @ A @ C @ B ) ) & 
% 36.37/36.58                          ( ~( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 36.37/36.58  thf('116', plain,
% 36.37/36.58      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 36.37/36.58         (~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X44))
% 36.37/36.58          | ~ (v5_waybel_6 @ X43 @ X44)
% 36.37/36.58          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ X44))
% 36.37/36.58          | ~ (r1_orders_2 @ X44 @ (k11_lattice3 @ X44 @ X46 @ X45) @ X43)
% 36.37/36.58          | (r1_orders_2 @ X44 @ X45 @ X43)
% 36.37/36.58          | (r1_orders_2 @ X44 @ X46 @ X43)
% 36.37/36.58          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X44))
% 36.37/36.58          | ~ (l1_orders_2 @ X44)
% 36.37/36.58          | (v2_struct_0 @ X44))),
% 36.37/36.58      inference('cnf', [status(esa)], [d6_waybel_6])).
% 36.37/36.58  thf('117', plain,
% 36.37/36.58      (![X0 : $i, X1 : $i]:
% 36.37/36.58         ((v2_struct_0 @ sk_A)
% 36.37/36.58          | ~ (l1_orders_2 @ sk_A)
% 36.37/36.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.58          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ X0 @ X1) @ sk_B)
% 36.37/36.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 36.37/36.58          | ~ (v5_waybel_6 @ sk_B @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['115', '116'])).
% 36.37/36.58  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('119', plain, ((v5_waybel_6 @ sk_B @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('120', plain,
% 36.37/36.58      (![X0 : $i, X1 : $i]:
% 36.37/36.58         ((v2_struct_0 @ sk_A)
% 36.37/36.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.58          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ X0 @ X1) @ sk_B)
% 36.37/36.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 36.37/36.58      inference('demod', [status(thm)], ['117', '118', '119'])).
% 36.37/36.58  thf('121', plain,
% 36.37/36.58      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 36.37/36.58        | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 36.37/36.58        | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 36.37/36.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 36.37/36.58        | (v2_struct_0 @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['114', '120'])).
% 36.37/36.58  thf('122', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('123', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('124', plain,
% 36.37/36.58      (((r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 36.37/36.58        | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 36.37/36.58        | (v2_struct_0 @ sk_A))),
% 36.37/36.58      inference('demod', [status(thm)], ['121', '122', '123'])).
% 36.37/36.58  thf('125', plain,
% 36.37/36.58      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 36.37/36.58      inference('simplify', [status(thm)], ['124'])).
% 36.37/36.58  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.58      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.58  thf('127', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 36.37/36.58      inference('clc', [status(thm)], ['125', '126'])).
% 36.37/36.58  thf('128', plain,
% 36.37/36.58      (((r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_B @ sk_B @ sk_A) @ sk_B)
% 36.37/36.58        | ((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.58        | (v2_struct_0 @ sk_A))),
% 36.37/36.58      inference('demod', [status(thm)], ['113', '127'])).
% 36.37/36.58  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.58      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.58  thf('130', plain,
% 36.37/36.58      ((((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.58        | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_B @ sk_B @ sk_A) @ sk_B))),
% 36.37/36.58      inference('clc', [status(thm)], ['128', '129'])).
% 36.37/36.58  thf('131', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('132', plain,
% 36.37/36.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 36.37/36.58         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 36.37/36.58          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 36.37/36.58          | ~ (r1_orders_2 @ X12 @ X13 @ X11)
% 36.37/36.58          | ~ (r1_orders_2 @ X12 @ X13 @ X14)
% 36.37/36.58          | ~ (r1_orders_2 @ X12 @ (sk_E @ X13 @ X14 @ X11 @ X12) @ X13)
% 36.37/36.58          | ((X13) = (k11_lattice3 @ X12 @ X11 @ X14))
% 36.37/36.58          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 36.37/36.58          | ~ (l1_orders_2 @ X12)
% 36.37/36.58          | ~ (v2_lattice3 @ X12)
% 36.37/36.58          | ~ (v5_orders_2 @ X12)
% 36.37/36.58          | (v2_struct_0 @ X12))),
% 36.37/36.58      inference('cnf', [status(esa)], [l28_lattice3])).
% 36.37/36.58  thf('133', plain,
% 36.37/36.58      (![X0 : $i, X1 : $i]:
% 36.37/36.58         ((v2_struct_0 @ sk_A)
% 36.37/36.58          | ~ (v5_orders_2 @ sk_A)
% 36.37/36.58          | ~ (v2_lattice3 @ sk_A)
% 36.37/36.58          | ~ (l1_orders_2 @ sk_A)
% 36.37/36.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.58          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X1)
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 36.37/36.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 36.37/36.58      inference('sup-', [status(thm)], ['131', '132'])).
% 36.37/36.58  thf('134', plain, ((v5_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('135', plain, ((v2_lattice3 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('136', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('137', plain,
% 36.37/36.58      (![X0 : $i, X1 : $i]:
% 36.37/36.58         ((v2_struct_0 @ sk_A)
% 36.37/36.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.58          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X1)
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 36.37/36.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 36.37/36.58      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 36.37/36.58  thf('138', plain,
% 36.37/36.58      ((((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 36.37/36.58        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 36.37/36.58        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 36.37/36.58        | ((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.58        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 36.37/36.58        | (v2_struct_0 @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['130', '137'])).
% 36.37/36.58  thf('139', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('140', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 36.37/36.58      inference('clc', [status(thm)], ['125', '126'])).
% 36.37/36.58  thf('141', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 36.37/36.58      inference('clc', [status(thm)], ['125', '126'])).
% 36.37/36.58  thf('142', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('143', plain,
% 36.37/36.58      ((((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.58        | ((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))
% 36.37/36.58        | (v2_struct_0 @ sk_A))),
% 36.37/36.58      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 36.37/36.58  thf('144', plain,
% 36.37/36.58      (((v2_struct_0 @ sk_A) | ((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B)))),
% 36.37/36.58      inference('simplify', [status(thm)], ['143'])).
% 36.37/36.58  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.58      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.58  thf('146', plain, (((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_B))),
% 36.37/36.58      inference('clc', [status(thm)], ['144', '145'])).
% 36.37/36.58  thf('147', plain,
% 36.37/36.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.37/36.58         ((zip_tseitin_1 @ X2 @ X1 @ X0 @ sk_A)
% 36.37/36.58          | (r1_orders_2 @ sk_A @ sk_B @ X2)
% 36.37/36.58          | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ X2))),
% 36.37/36.58      inference('demod', [status(thm)], ['101', '146'])).
% 36.37/36.58  thf('148', plain,
% 36.37/36.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.37/36.58         ((zip_tseitin_1 @ X0 @ (k5_waybel_0 @ sk_A @ sk_B) @ X3 @ sk_A)
% 36.37/36.58          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 36.37/36.58          | (zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['65', '147'])).
% 36.37/36.58  thf('149', plain,
% 36.37/36.58      (![X0 : $i, X1 : $i]:
% 36.37/36.58         ((zip_tseitin_1 @ X1 @ (k5_waybel_0 @ sk_A @ sk_B) @ X0 @ sk_A)
% 36.37/36.58          | (r1_orders_2 @ sk_A @ sk_B @ X1))),
% 36.37/36.58      inference('condensation', [status(thm)], ['148'])).
% 36.37/36.58  thf('150', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 36.37/36.58  thf(zf_stmt_4, axiom,
% 36.37/36.58    (![C:$i,B:$i,A:$i]:
% 36.37/36.58     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 36.37/36.58       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 36.37/36.58  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 36.37/36.58  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 36.37/36.58  thf(zf_stmt_7, axiom,
% 36.37/36.58    (![A:$i]:
% 36.37/36.58     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 36.37/36.58       ( ![B:$i]:
% 36.37/36.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.58           ( ![C:$i]:
% 36.37/36.58             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 36.37/36.58                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 36.37/36.58                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 36.37/36.58               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 36.37/36.58                   ( r1_yellow_0 @ A @ C ) ) =>
% 36.37/36.58                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 36.37/36.58                   ( ![D:$i]:
% 36.37/36.58                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 36.37/36.58                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 36.37/36.58                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 36.37/36.58  thf('151', plain,
% 36.37/36.58      (![X29 : $i, X30 : $i, X33 : $i]:
% 36.37/36.58         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 36.37/36.58          | ~ (r2_lattice3 @ X30 @ X33 @ X29)
% 36.37/36.58          | ~ (zip_tseitin_1 @ (sk_D_1 @ X33 @ X29 @ X30) @ X33 @ X29 @ X30)
% 36.37/36.58          | (zip_tseitin_2 @ X33 @ X29 @ X30)
% 36.37/36.58          | ~ (l1_orders_2 @ X30)
% 36.37/36.58          | ~ (v5_orders_2 @ X30))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_7])).
% 36.37/36.58  thf('152', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         (~ (v5_orders_2 @ sk_A)
% 36.37/36.58          | ~ (l1_orders_2 @ sk_A)
% 36.37/36.58          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 36.37/36.58          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 36.37/36.58          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 36.37/36.58      inference('sup-', [status(thm)], ['150', '151'])).
% 36.37/36.58  thf('153', plain, ((v5_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('154', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('155', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 36.37/36.58          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 36.37/36.58          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 36.37/36.58      inference('demod', [status(thm)], ['152', '153', '154'])).
% 36.37/36.58  thf('156', plain,
% 36.37/36.58      (((r1_orders_2 @ sk_A @ sk_B @ 
% 36.37/36.58         (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 36.37/36.58        | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 36.37/36.58        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['149', '155'])).
% 36.37/36.58  thf('157', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('158', plain,
% 36.37/36.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 36.37/36.58         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 36.37/36.58          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ (u1_struct_0 @ X5))
% 36.37/36.58          | (r2_lattice3 @ X5 @ X6 @ X4)
% 36.37/36.58          | ~ (l1_orders_2 @ X5))),
% 36.37/36.58      inference('cnf', [status(esa)], [d9_lattice3])).
% 36.37/36.58  thf('159', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         (~ (l1_orders_2 @ sk_A)
% 36.37/36.58          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 36.37/36.58      inference('sup-', [status(thm)], ['157', '158'])).
% 36.37/36.58  thf('160', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('161', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 36.37/36.58      inference('demod', [status(thm)], ['159', '160'])).
% 36.37/36.58  thf('162', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('163', plain,
% 36.37/36.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 36.37/36.58         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 36.37/36.58          | (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 36.37/36.58          | (r2_lattice3 @ X5 @ X6 @ X4)
% 36.37/36.58          | ~ (l1_orders_2 @ X5))),
% 36.37/36.58      inference('cnf', [status(esa)], [d9_lattice3])).
% 36.37/36.58  thf('164', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         (~ (l1_orders_2 @ sk_A)
% 36.37/36.58          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 36.37/36.58      inference('sup-', [status(thm)], ['162', '163'])).
% 36.37/36.58  thf('165', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('166', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 36.37/36.58      inference('demod', [status(thm)], ['164', '165'])).
% 36.37/36.58  thf('167', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('168', plain,
% 36.37/36.58      (![X40 : $i, X41 : $i, X42 : $i]:
% 36.37/36.58         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 36.37/36.58          | ~ (r2_hidden @ X42 @ (k5_waybel_0 @ X41 @ X40))
% 36.37/36.58          | (r1_orders_2 @ X41 @ X42 @ X40)
% 36.37/36.58          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 36.37/36.58          | ~ (l1_orders_2 @ X41)
% 36.37/36.58          | (v2_struct_0 @ X41))),
% 36.37/36.58      inference('cnf', [status(esa)], [t17_waybel_0])).
% 36.37/36.58  thf('169', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((v2_struct_0 @ sk_A)
% 36.37/36.58          | ~ (l1_orders_2 @ sk_A)
% 36.37/36.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.58          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | ~ (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 36.37/36.58      inference('sup-', [status(thm)], ['167', '168'])).
% 36.37/36.58  thf('170', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('171', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((v2_struct_0 @ sk_A)
% 36.37/36.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.37/36.58          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | ~ (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 36.37/36.58      inference('demod', [status(thm)], ['169', '170'])).
% 36.37/36.58  thf('172', plain,
% 36.37/36.58      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 36.37/36.58        | (r1_orders_2 @ sk_A @ 
% 36.37/36.58           (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 36.37/36.58        | ~ (m1_subset_1 @ 
% 36.37/36.58             (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ 
% 36.37/36.58             (u1_struct_0 @ sk_A))
% 36.37/36.58        | (v2_struct_0 @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['166', '171'])).
% 36.37/36.58  thf('173', plain,
% 36.37/36.58      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 36.37/36.58        | (v2_struct_0 @ sk_A)
% 36.37/36.58        | (r1_orders_2 @ sk_A @ 
% 36.37/36.58           (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 36.37/36.58        | (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B))),
% 36.37/36.58      inference('sup-', [status(thm)], ['161', '172'])).
% 36.37/36.58  thf('174', plain,
% 36.37/36.58      (((r1_orders_2 @ sk_A @ 
% 36.37/36.58         (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 36.37/36.58        | (v2_struct_0 @ sk_A)
% 36.37/36.58        | (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B))),
% 36.37/36.58      inference('simplify', [status(thm)], ['173'])).
% 36.37/36.58  thf('175', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('176', plain,
% 36.37/36.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 36.37/36.58         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 36.37/36.58          | ~ (r1_orders_2 @ X5 @ (sk_D @ X4 @ X6 @ X5) @ X4)
% 36.37/36.58          | (r2_lattice3 @ X5 @ X6 @ X4)
% 36.37/36.58          | ~ (l1_orders_2 @ X5))),
% 36.37/36.58      inference('cnf', [status(esa)], [d9_lattice3])).
% 36.37/36.58  thf('177', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         (~ (l1_orders_2 @ sk_A)
% 36.37/36.58          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 36.37/36.58      inference('sup-', [status(thm)], ['175', '176'])).
% 36.37/36.58  thf('178', plain, ((l1_orders_2 @ sk_A)),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.37/36.58  thf('179', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 36.37/36.58          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 36.37/36.58      inference('demod', [status(thm)], ['177', '178'])).
% 36.37/36.58  thf('180', plain,
% 36.37/36.58      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 36.37/36.58        | (v2_struct_0 @ sk_A))),
% 36.37/36.58      inference('clc', [status(thm)], ['174', '179'])).
% 36.37/36.58  thf('181', plain, (~ (v2_struct_0 @ sk_A)),
% 36.37/36.58      inference('demod', [status(thm)], ['9', '10'])).
% 36.37/36.58  thf('182', plain,
% 36.37/36.58      ((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 36.37/36.58      inference('clc', [status(thm)], ['180', '181'])).
% 36.37/36.58  thf('183', plain,
% 36.37/36.58      (((r1_orders_2 @ sk_A @ sk_B @ 
% 36.37/36.58         (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 36.37/36.58        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 36.37/36.58      inference('demod', [status(thm)], ['156', '182'])).
% 36.37/36.58  thf('184', plain,
% 36.37/36.58      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 36.37/36.58         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 36.37/36.58          | ~ (r1_orders_2 @ X21 @ X20 @ X18))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 36.37/36.58  thf('185', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 36.37/36.58          | (zip_tseitin_0 @ 
% 36.37/36.58             (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A) @ X0 @ 
% 36.37/36.58             sk_B @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['183', '184'])).
% 36.37/36.58  thf('186', plain,
% 36.37/36.58      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 36.37/36.58         ((zip_tseitin_1 @ X22 @ X23 @ X24 @ X25)
% 36.37/36.58          | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 36.37/36.58  thf('187', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 36.37/36.58          | (zip_tseitin_1 @ 
% 36.37/36.58             (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A) @ X0 @ 
% 36.37/36.58             sk_B @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['185', '186'])).
% 36.37/36.58  thf('188', plain,
% 36.37/36.58      (![X0 : $i]:
% 36.37/36.58         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 36.37/36.58          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 36.37/36.58          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 36.37/36.58      inference('demod', [status(thm)], ['152', '153', '154'])).
% 36.37/36.58  thf('189', plain,
% 36.37/36.58      (((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 36.37/36.58        | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 36.37/36.58        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 36.37/36.58      inference('sup-', [status(thm)], ['187', '188'])).
% 36.37/36.58  thf('190', plain,
% 36.37/36.58      ((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 36.37/36.58      inference('clc', [status(thm)], ['180', '181'])).
% 36.37/36.58  thf('191', plain,
% 36.37/36.58      (((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 36.37/36.58        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 36.37/36.58      inference('demod', [status(thm)], ['189', '190'])).
% 36.37/36.58  thf('192', plain,
% 36.37/36.58      ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)),
% 36.37/36.58      inference('simplify', [status(thm)], ['191'])).
% 36.37/36.58  thf('193', plain,
% 36.37/36.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 36.37/36.58         (((X28) = (k1_yellow_0 @ X26 @ X27))
% 36.37/36.58          | ~ (zip_tseitin_2 @ X27 @ X28 @ X26))),
% 36.37/36.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 36.37/36.58  thf('194', plain,
% 36.37/36.58      (((sk_B) = (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 36.37/36.58      inference('sup-', [status(thm)], ['192', '193'])).
% 36.37/36.58  thf('195', plain, ((v4_waybel_7 @ sk_B @ sk_A)),
% 36.37/36.58      inference('demod', [status(thm)], ['62', '194'])).
% 36.37/36.58  thf('196', plain, ($false), inference('demod', [status(thm)], ['0', '195'])).
% 36.37/36.58  
% 36.37/36.58  % SZS output end Refutation
% 36.37/36.58  
% 36.37/36.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
