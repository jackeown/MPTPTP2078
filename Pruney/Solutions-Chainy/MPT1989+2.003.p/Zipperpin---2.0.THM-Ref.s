%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vyDbJdJvnD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:18 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 628 expanded)
%              Number of leaves         :   47 ( 200 expanded)
%              Depth                    :   20
%              Number of atoms          : 1631 (8812 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_waybel_6_type,type,(
    v5_waybel_6: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v4_waybel_7_type,type,(
    v4_waybel_7: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ~ ( v1_lattice3 @ X5 )
      | ~ ( v2_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('8',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','10'])).

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

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( X35
       != ( k1_yellow_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v1_waybel_7 @ X37 @ X36 )
      | ~ ( v12_waybel_0 @ X37 @ X36 )
      | ~ ( v1_waybel_0 @ X37 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ( v4_waybel_7 @ X35 @ X36 )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v2_lattice3 @ X36 )
      | ~ ( v1_lattice3 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v3_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v1_lattice3 @ X36 )
      | ~ ( v2_lattice3 @ X36 )
      | ~ ( l1_orders_2 @ X36 )
      | ( v4_waybel_7 @ ( k1_yellow_0 @ X36 @ X37 ) @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( v1_waybel_0 @ X37 @ X36 )
      | ~ ( v12_waybel_0 @ X37 @ X36 )
      | ~ ( v1_waybel_7 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X36 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
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
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ( v1_waybel_7 @ ( k5_waybel_0 @ X39 @ X38 ) @ X39 )
      | ~ ( v5_waybel_6 @ X38 @ X39 )
      | ~ ( l1_orders_2 @ X39 )
      | ~ ( v2_lattice3 @ X39 )
      | ~ ( v1_lattice3 @ X39 )
      | ~ ( v5_orders_2 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v3_orders_2 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t37_waybel_7])).

thf('17',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_6 @ sk_B @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_waybel_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['17','18','19','20','21','22','23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc12_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) )).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( v12_waybel_0 @ ( k5_waybel_0 @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc12_waybel_0])).

thf('28',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('33',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X30 )
      | ~ ( v3_orders_2 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( v1_waybel_0 @ ( k5_waybel_0 @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('36',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('41',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','25','33','41','42','43','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X30 )
      | ~ ( v3_orders_2 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_xboole_0 @ ( k5_waybel_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r1_orders_2 @ X33 @ X34 @ X32 )
      | ( r2_hidden @ X34 @ ( k5_waybel_0 @ X33 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X3 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('72',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('75',plain,(
    r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

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

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_lattice3 @ X13 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('78',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X17 ) ) ) ),
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

thf('79',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r2_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_orders_2 @ X7 @ X9 @ X6 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_1 @ X1 @ X5 @ X4 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 @ X4 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','84'])).

thf('86',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ( zip_tseitin_1 @ X1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X1 ) ) ),
    inference(condensation,[status(thm)],['87'])).

thf('89',plain,(
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

thf('90',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_lattice3 @ X22 @ X25 @ X21 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X21 @ X22 ) @ X25 @ X21 @ X22 )
      | ( zip_tseitin_2 @ X25 @ X21 @ X22 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X8 @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ( r2_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ( r2_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r2_hidden @ X34 @ ( k5_waybel_0 @ X33 @ X32 ) )
      | ( r1_orders_2 @ X33 @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['100','111'])).

thf('113',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_orders_2 @ X7 @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ( r2_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['113','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('121',plain,(
    r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['95','121'])).

thf('123',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ~ ( r1_orders_2 @ X13 @ X12 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('128',plain,
    ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['119','120'])).

thf('130',plain,
    ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X20
        = ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('133',plain,
    ( sk_B
    = ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( sk_B
    = ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v4_waybel_7 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['57','133','134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['0','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vyDbJdJvnD
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.77  % Solved by: fo/fo7.sh
% 0.54/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.77  % done 287 iterations in 0.321s
% 0.54/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.77  % SZS output start Refutation
% 0.54/0.77  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.54/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.77  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.54/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.77  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.54/0.77  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.54/0.77  thf(v12_waybel_0_type, type, v12_waybel_0: $i > $i > $o).
% 0.54/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.77  thf(v5_waybel_6_type, type, v5_waybel_6: $i > $i > $o).
% 0.54/0.77  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.54/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.54/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.54/0.77  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.54/0.77  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.54/0.77  thf(v4_waybel_7_type, type, v4_waybel_7: $i > $i > $o).
% 0.54/0.77  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.54/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.77  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.54/0.77  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.54/0.77  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.54/0.77  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 0.54/0.77  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.54/0.77  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.54/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.77  thf(v1_waybel_7_type, type, v1_waybel_7: $i > $i > $o).
% 0.54/0.77  thf(v1_waybel_0_type, type, v1_waybel_0: $i > $i > $o).
% 0.54/0.77  thf(t38_waybel_7, conjecture,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.54/0.77         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ))).
% 0.54/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.77    (~( ![A:$i]:
% 0.54/0.77        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.54/0.77            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.77          ( ![B:$i]:
% 0.54/0.77            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77              ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ) )),
% 0.54/0.77    inference('cnf.neg', [status(esa)], [t38_waybel_7])).
% 0.54/0.77  thf('0', plain, (~ (v4_waybel_7 @ sk_B @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(dt_k5_waybel_0, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.54/0.77         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77       ( m1_subset_1 @
% 0.54/0.77         ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.54/0.77  thf('2', plain,
% 0.54/0.77      (![X26 : $i, X27 : $i]:
% 0.54/0.77         (~ (l1_orders_2 @ X26)
% 0.54/0.77          | (v2_struct_0 @ X26)
% 0.54/0.77          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.54/0.77          | (m1_subset_1 @ (k5_waybel_0 @ X26 @ X27) @ 
% 0.54/0.77             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.54/0.77      inference('cnf', [status(esa)], [dt_k5_waybel_0])).
% 0.54/0.77  thf('3', plain,
% 0.54/0.77      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.54/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.77        | (v2_struct_0 @ sk_A)
% 0.54/0.77        | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.77  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('5', plain,
% 0.54/0.77      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.54/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['3', '4'])).
% 0.54/0.77  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(cc1_lattice3, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( l1_orders_2 @ A ) =>
% 0.54/0.77       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.54/0.77  thf('7', plain,
% 0.54/0.77      (![X5 : $i]:
% 0.54/0.77         (~ (v1_lattice3 @ X5) | ~ (v2_struct_0 @ X5) | ~ (l1_orders_2 @ X5))),
% 0.54/0.77      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.54/0.77  thf('8', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.54/0.77  thf('9', plain, ((v1_lattice3 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.77  thf('11', plain,
% 0.54/0.77      ((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.54/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('clc', [status(thm)], ['5', '10'])).
% 0.54/0.77  thf(d6_waybel_7, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.54/0.77         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ( v4_waybel_7 @ B @ A ) <=>
% 0.54/0.77             ( ?[C:$i]:
% 0.54/0.77               ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.54/0.77                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.54/0.77                 ( v1_waybel_7 @ C @ A ) & ( v12_waybel_0 @ C @ A ) & 
% 0.54/0.77                 ( v1_waybel_0 @ C @ A ) & ( ~( v1_xboole_0 @ C ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('12', plain,
% 0.54/0.77      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 0.54/0.77          | ((X35) != (k1_yellow_0 @ X36 @ X37))
% 0.54/0.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.54/0.77          | ~ (v1_waybel_7 @ X37 @ X36)
% 0.54/0.77          | ~ (v12_waybel_0 @ X37 @ X36)
% 0.54/0.77          | ~ (v1_waybel_0 @ X37 @ X36)
% 0.54/0.77          | (v1_xboole_0 @ X37)
% 0.54/0.77          | (v4_waybel_7 @ X35 @ X36)
% 0.54/0.77          | ~ (l1_orders_2 @ X36)
% 0.54/0.77          | ~ (v2_lattice3 @ X36)
% 0.54/0.77          | ~ (v1_lattice3 @ X36)
% 0.54/0.77          | ~ (v5_orders_2 @ X36)
% 0.54/0.77          | ~ (v4_orders_2 @ X36)
% 0.54/0.77          | ~ (v3_orders_2 @ X36))),
% 0.54/0.77      inference('cnf', [status(esa)], [d6_waybel_7])).
% 0.54/0.77  thf('13', plain,
% 0.54/0.77      (![X36 : $i, X37 : $i]:
% 0.54/0.77         (~ (v3_orders_2 @ X36)
% 0.54/0.77          | ~ (v4_orders_2 @ X36)
% 0.54/0.77          | ~ (v5_orders_2 @ X36)
% 0.54/0.77          | ~ (v1_lattice3 @ X36)
% 0.54/0.77          | ~ (v2_lattice3 @ X36)
% 0.54/0.77          | ~ (l1_orders_2 @ X36)
% 0.54/0.77          | (v4_waybel_7 @ (k1_yellow_0 @ X36 @ X37) @ X36)
% 0.54/0.77          | (v1_xboole_0 @ X37)
% 0.54/0.77          | ~ (v1_waybel_0 @ X37 @ X36)
% 0.54/0.77          | ~ (v12_waybel_0 @ X37 @ X36)
% 0.54/0.77          | ~ (v1_waybel_7 @ X37 @ X36)
% 0.54/0.77          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.54/0.77          | ~ (m1_subset_1 @ (k1_yellow_0 @ X36 @ X37) @ (u1_struct_0 @ X36)))),
% 0.54/0.77      inference('simplify', [status(thm)], ['12'])).
% 0.54/0.77  thf('14', plain,
% 0.54/0.77      ((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.54/0.77           (u1_struct_0 @ sk_A))
% 0.54/0.77        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.54/0.77        | ~ (v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.54/0.77        | ~ (v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.54/0.77        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.54/0.77        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.54/0.77           sk_A)
% 0.54/0.77        | ~ (l1_orders_2 @ sk_A)
% 0.54/0.77        | ~ (v2_lattice3 @ sk_A)
% 0.54/0.77        | ~ (v1_lattice3 @ sk_A)
% 0.54/0.77        | ~ (v5_orders_2 @ sk_A)
% 0.54/0.77        | ~ (v4_orders_2 @ sk_A)
% 0.54/0.77        | ~ (v3_orders_2 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['11', '13'])).
% 0.54/0.77  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(t37_waybel_7, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.54/0.77         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ( v5_waybel_6 @ B @ A ) =>
% 0.54/0.77             ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.54/0.77  thf('16', plain,
% 0.54/0.77      (![X38 : $i, X39 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X39))
% 0.54/0.77          | (v1_waybel_7 @ (k5_waybel_0 @ X39 @ X38) @ X39)
% 0.54/0.77          | ~ (v5_waybel_6 @ X38 @ X39)
% 0.54/0.77          | ~ (l1_orders_2 @ X39)
% 0.54/0.77          | ~ (v2_lattice3 @ X39)
% 0.54/0.77          | ~ (v1_lattice3 @ X39)
% 0.54/0.77          | ~ (v5_orders_2 @ X39)
% 0.54/0.77          | ~ (v4_orders_2 @ X39)
% 0.54/0.77          | ~ (v3_orders_2 @ X39))),
% 0.54/0.77      inference('cnf', [status(esa)], [t37_waybel_7])).
% 0.54/0.77  thf('17', plain,
% 0.54/0.77      ((~ (v3_orders_2 @ sk_A)
% 0.54/0.77        | ~ (v4_orders_2 @ sk_A)
% 0.54/0.77        | ~ (v5_orders_2 @ sk_A)
% 0.54/0.77        | ~ (v1_lattice3 @ sk_A)
% 0.54/0.77        | ~ (v2_lattice3 @ sk_A)
% 0.54/0.77        | ~ (l1_orders_2 @ sk_A)
% 0.54/0.77        | ~ (v5_waybel_6 @ sk_B @ sk_A)
% 0.54/0.77        | (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.77  thf('18', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('21', plain, ((v1_lattice3 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('22', plain, ((v2_lattice3 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('24', plain, ((v5_waybel_6 @ sk_B @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('25', plain, ((v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)],
% 0.54/0.77                ['17', '18', '19', '20', '21', '22', '23', '24'])).
% 0.54/0.77  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(fc12_waybel_0, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_orders_2 @ A ) & 
% 0.54/0.77         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77       ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ))).
% 0.54/0.77  thf('27', plain,
% 0.54/0.77      (![X28 : $i, X29 : $i]:
% 0.54/0.77         (~ (l1_orders_2 @ X28)
% 0.54/0.77          | ~ (v4_orders_2 @ X28)
% 0.54/0.77          | (v2_struct_0 @ X28)
% 0.54/0.77          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.54/0.77          | (v12_waybel_0 @ (k5_waybel_0 @ X28 @ X29) @ X28))),
% 0.54/0.77      inference('cnf', [status(esa)], [fc12_waybel_0])).
% 0.54/0.77  thf('28', plain,
% 0.54/0.77      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.54/0.77        | (v2_struct_0 @ sk_A)
% 0.54/0.77        | ~ (v4_orders_2 @ sk_A)
% 0.54/0.77        | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.77  thf('29', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('31', plain,
% 0.54/0.77      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.54/0.77  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.77  thf('33', plain, ((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.54/0.77      inference('clc', [status(thm)], ['31', '32'])).
% 0.54/0.77  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(fc8_waybel_0, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.54/0.77         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.77       ( ( ~( v1_xboole_0 @ ( k5_waybel_0 @ A @ B ) ) ) & 
% 0.54/0.77         ( v1_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ))).
% 0.54/0.77  thf('35', plain,
% 0.54/0.77      (![X30 : $i, X31 : $i]:
% 0.54/0.77         (~ (l1_orders_2 @ X30)
% 0.54/0.77          | ~ (v3_orders_2 @ X30)
% 0.54/0.77          | (v2_struct_0 @ X30)
% 0.54/0.77          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.54/0.77          | (v1_waybel_0 @ (k5_waybel_0 @ X30 @ X31) @ X30))),
% 0.54/0.77      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 0.54/0.77  thf('36', plain,
% 0.54/0.77      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.54/0.77        | (v2_struct_0 @ sk_A)
% 0.54/0.77        | ~ (v3_orders_2 @ sk_A)
% 0.54/0.77        | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.54/0.77  thf('37', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('39', plain,
% 0.54/0.77      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.54/0.77  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.77  thf('41', plain, ((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.54/0.77      inference('clc', [status(thm)], ['39', '40'])).
% 0.54/0.77  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('43', plain, ((v2_lattice3 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('44', plain, ((v1_lattice3 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('45', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('46', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('47', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('48', plain,
% 0.54/0.77      ((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.54/0.77           (u1_struct_0 @ sk_A))
% 0.54/0.77        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.54/0.77        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.54/0.77           sk_A))),
% 0.54/0.77      inference('demod', [status(thm)],
% 0.54/0.77                ['14', '25', '33', '41', '42', '43', '44', '45', '46', '47'])).
% 0.54/0.77  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('50', plain,
% 0.54/0.77      (![X30 : $i, X31 : $i]:
% 0.54/0.77         (~ (l1_orders_2 @ X30)
% 0.54/0.77          | ~ (v3_orders_2 @ X30)
% 0.54/0.77          | (v2_struct_0 @ X30)
% 0.54/0.77          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.54/0.77          | ~ (v1_xboole_0 @ (k5_waybel_0 @ X30 @ X31)))),
% 0.54/0.77      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 0.54/0.77  thf('51', plain,
% 0.54/0.77      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.54/0.77        | (v2_struct_0 @ sk_A)
% 0.54/0.77        | ~ (v3_orders_2 @ sk_A)
% 0.54/0.77        | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['49', '50'])).
% 0.54/0.77  thf('52', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('54', plain,
% 0.54/0.77      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.54/0.77  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.77  thf('56', plain, (~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))),
% 0.54/0.77      inference('clc', [status(thm)], ['54', '55'])).
% 0.54/0.77  thf('57', plain,
% 0.54/0.77      (((v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.54/0.77         sk_A)
% 0.54/0.77        | ~ (m1_subset_1 @ 
% 0.54/0.77             (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.54/0.77             (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('clc', [status(thm)], ['48', '56'])).
% 0.54/0.77  thf('58', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(t17_waybel_0, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77               ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) ) <=>
% 0.54/0.77                 ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.54/0.77  thf('60', plain,
% 0.54/0.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 0.54/0.77          | ~ (r1_orders_2 @ X33 @ X34 @ X32)
% 0.54/0.77          | (r2_hidden @ X34 @ (k5_waybel_0 @ X33 @ X32))
% 0.54/0.77          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.54/0.77          | ~ (l1_orders_2 @ X33)
% 0.54/0.77          | (v2_struct_0 @ X33))),
% 0.54/0.77      inference('cnf', [status(esa)], [t17_waybel_0])).
% 0.54/0.77  thf('61', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.77          | (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.54/0.77          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.54/0.77      inference('sup-', [status(thm)], ['59', '60'])).
% 0.54/0.77  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('63', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.77          | (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.54/0.77          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['61', '62'])).
% 0.54/0.77  thf('64', plain,
% 0.54/0.77      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.54/0.77        | (r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['58', '63'])).
% 0.54/0.77  thf('65', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(t24_orders_2, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.54/0.77  thf('66', plain,
% 0.54/0.77      (![X3 : $i, X4 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.54/0.77          | (r1_orders_2 @ X4 @ X3 @ X3)
% 0.54/0.77          | ~ (l1_orders_2 @ X4)
% 0.54/0.77          | ~ (v3_orders_2 @ X4)
% 0.54/0.77          | (v2_struct_0 @ X4))),
% 0.54/0.77      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.54/0.77  thf('67', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_A)
% 0.54/0.77        | ~ (v3_orders_2 @ sk_A)
% 0.54/0.77        | ~ (l1_orders_2 @ sk_A)
% 0.54/0.77        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.54/0.77      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.77  thf('68', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('70', plain,
% 0.54/0.77      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.54/0.77  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.77  thf('72', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.54/0.77      inference('clc', [status(thm)], ['70', '71'])).
% 0.54/0.77  thf('73', plain,
% 0.54/0.77      (((r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['64', '72'])).
% 0.54/0.77  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.77  thf('75', plain, ((r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B))),
% 0.54/0.77      inference('clc', [status(thm)], ['73', '74'])).
% 0.54/0.77  thf(t30_yellow_0, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.54/0.77                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.54/0.77                 ( ( ![D:$i]:
% 0.54/0.77                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.54/0.77                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.54/0.77                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.54/0.77               ( ( ( ![D:$i]:
% 0.54/0.77                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.54/0.77                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.54/0.77                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.54/0.77                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.54/0.77                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf(zf_stmt_1, axiom,
% 0.54/0.77    (![D:$i,C:$i,B:$i,A:$i]:
% 0.54/0.77     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.54/0.77       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.54/0.77  thf('76', plain,
% 0.54/0.77      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.77         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.54/0.77          | (r2_lattice3 @ X13 @ X11 @ X10))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.77  thf('77', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(zf_stmt_2, axiom,
% 0.54/0.77    (![D:$i,C:$i,B:$i,A:$i]:
% 0.54/0.77     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.54/0.77       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.54/0.77  thf('78', plain,
% 0.54/0.77      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.54/0.77         ((zip_tseitin_1 @ X14 @ X15 @ X16 @ X17)
% 0.54/0.77          | (m1_subset_1 @ X14 @ (u1_struct_0 @ X17)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.77  thf(d9_lattice3, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( l1_orders_2 @ A ) =>
% 0.54/0.77       ( ![B:$i,C:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.54/0.77             ( ![D:$i]:
% 0.54/0.77               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('79', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.54/0.77          | ~ (r2_lattice3 @ X7 @ X8 @ X6)
% 0.54/0.77          | ~ (r2_hidden @ X9 @ X8)
% 0.54/0.77          | (r1_orders_2 @ X7 @ X9 @ X6)
% 0.54/0.77          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.54/0.77          | ~ (l1_orders_2 @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.54/0.77  thf('80', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.77         ((zip_tseitin_1 @ X1 @ X5 @ X4 @ X0)
% 0.54/0.77          | ~ (l1_orders_2 @ X0)
% 0.54/0.77          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.54/0.77          | (r1_orders_2 @ X0 @ X2 @ X1)
% 0.54/0.77          | ~ (r2_hidden @ X2 @ X3)
% 0.54/0.77          | ~ (r2_lattice3 @ X0 @ X3 @ X1))),
% 0.54/0.77      inference('sup-', [status(thm)], ['78', '79'])).
% 0.54/0.77  thf('81', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.77         (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 0.54/0.77          | ~ (r2_hidden @ sk_B @ X1)
% 0.54/0.77          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.54/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.77          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['77', '80'])).
% 0.54/0.77  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('83', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.77         (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 0.54/0.77          | ~ (r2_hidden @ sk_B @ X1)
% 0.54/0.77          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.54/0.77          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['81', '82'])).
% 0.54/0.77  thf('84', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.77         ((zip_tseitin_0 @ X0 @ X1 @ X4 @ sk_A)
% 0.54/0.77          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 0.54/0.77          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.54/0.77          | ~ (r2_hidden @ sk_B @ X1))),
% 0.54/0.77      inference('sup-', [status(thm)], ['76', '83'])).
% 0.54/0.77  thf('85', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.77         ((r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.54/0.77          | (zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A)
% 0.54/0.77          | (zip_tseitin_0 @ X0 @ (k5_waybel_0 @ sk_A @ sk_B) @ X3 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['75', '84'])).
% 0.54/0.77  thf('86', plain,
% 0.54/0.77      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.54/0.77         ((zip_tseitin_1 @ X14 @ X15 @ X16 @ X17)
% 0.54/0.77          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.77  thf('87', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.77         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 0.54/0.77          | (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.54/0.77          | (zip_tseitin_1 @ X1 @ (k5_waybel_0 @ sk_A @ sk_B) @ X0 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['85', '86'])).
% 0.54/0.77  thf('88', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         ((zip_tseitin_1 @ X1 @ (k5_waybel_0 @ sk_A @ sk_B) @ X0 @ sk_A)
% 0.54/0.77          | (r1_orders_2 @ sk_A @ sk_B @ X1))),
% 0.54/0.77      inference('condensation', [status(thm)], ['87'])).
% 0.54/0.77  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.54/0.77  thf(zf_stmt_4, axiom,
% 0.54/0.77    (![C:$i,B:$i,A:$i]:
% 0.54/0.77     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.54/0.77       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.54/0.77  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.54/0.77  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.54/0.77  thf(zf_stmt_7, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.54/0.77                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.54/0.77                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.54/0.77               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.54/0.77                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.54/0.77                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.54/0.77                   ( ![D:$i]:
% 0.54/0.77                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.77                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.54/0.77                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf('90', plain,
% 0.54/0.77      (![X21 : $i, X22 : $i, X25 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.54/0.77          | ~ (r2_lattice3 @ X22 @ X25 @ X21)
% 0.54/0.77          | ~ (zip_tseitin_1 @ (sk_D_1 @ X25 @ X21 @ X22) @ X25 @ X21 @ X22)
% 0.54/0.77          | (zip_tseitin_2 @ X25 @ X21 @ X22)
% 0.54/0.77          | ~ (l1_orders_2 @ X22)
% 0.54/0.77          | ~ (v5_orders_2 @ X22))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.54/0.77  thf('91', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (v5_orders_2 @ sk_A)
% 0.54/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.77          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.54/0.77          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.54/0.77          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.54/0.77      inference('sup-', [status(thm)], ['89', '90'])).
% 0.54/0.77  thf('92', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('93', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('94', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.54/0.77          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.54/0.77          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.54/0.77  thf('95', plain,
% 0.54/0.77      (((r1_orders_2 @ sk_A @ sk_B @ 
% 0.54/0.77         (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.54/0.77        | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.54/0.77        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['88', '94'])).
% 0.54/0.77  thf('96', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('97', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.54/0.77          | (m1_subset_1 @ (sk_D @ X6 @ X8 @ X7) @ (u1_struct_0 @ X7))
% 0.54/0.77          | (r2_lattice3 @ X7 @ X8 @ X6)
% 0.54/0.77          | ~ (l1_orders_2 @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.54/0.77  thf('98', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (l1_orders_2 @ sk_A)
% 0.54/0.77          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.54/0.77          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['96', '97'])).
% 0.54/0.77  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('100', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.54/0.77          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['98', '99'])).
% 0.54/0.77  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('102', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.54/0.77          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 0.54/0.77          | (r2_lattice3 @ X7 @ X8 @ X6)
% 0.54/0.77          | ~ (l1_orders_2 @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.54/0.77  thf('103', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (l1_orders_2 @ sk_A)
% 0.54/0.77          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.54/0.77          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['101', '102'])).
% 0.54/0.77  thf('104', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('105', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.54/0.77          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.54/0.77      inference('demod', [status(thm)], ['103', '104'])).
% 0.54/0.77  thf('106', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('107', plain,
% 0.54/0.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 0.54/0.77          | ~ (r2_hidden @ X34 @ (k5_waybel_0 @ X33 @ X32))
% 0.54/0.77          | (r1_orders_2 @ X33 @ X34 @ X32)
% 0.54/0.77          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.54/0.77          | ~ (l1_orders_2 @ X33)
% 0.54/0.77          | (v2_struct_0 @ X33))),
% 0.54/0.77      inference('cnf', [status(esa)], [t17_waybel_0])).
% 0.54/0.77  thf('108', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.77          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.54/0.77          | ~ (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['106', '107'])).
% 0.54/0.77  thf('109', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('110', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((v2_struct_0 @ sk_A)
% 0.54/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.77          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.54/0.77          | ~ (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('demod', [status(thm)], ['108', '109'])).
% 0.54/0.77  thf('111', plain,
% 0.54/0.77      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.54/0.77        | (r1_orders_2 @ sk_A @ 
% 0.54/0.77           (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.54/0.77        | ~ (m1_subset_1 @ 
% 0.54/0.77             (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ 
% 0.54/0.77             (u1_struct_0 @ sk_A))
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['105', '110'])).
% 0.54/0.77  thf('112', plain,
% 0.54/0.77      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.54/0.77        | (v2_struct_0 @ sk_A)
% 0.54/0.77        | (r1_orders_2 @ sk_A @ 
% 0.54/0.77           (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.54/0.77        | (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B))),
% 0.54/0.77      inference('sup-', [status(thm)], ['100', '111'])).
% 0.54/0.77  thf('113', plain,
% 0.54/0.77      (((r1_orders_2 @ sk_A @ 
% 0.54/0.77         (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.54/0.77        | (v2_struct_0 @ sk_A)
% 0.54/0.77        | (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B))),
% 0.54/0.77      inference('simplify', [status(thm)], ['112'])).
% 0.54/0.77  thf('114', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('115', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.54/0.77          | ~ (r1_orders_2 @ X7 @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 0.54/0.77          | (r2_lattice3 @ X7 @ X8 @ X6)
% 0.54/0.77          | ~ (l1_orders_2 @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.54/0.77  thf('116', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (l1_orders_2 @ sk_A)
% 0.54/0.77          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.54/0.77          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.54/0.77      inference('sup-', [status(thm)], ['114', '115'])).
% 0.54/0.77  thf('117', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('118', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.54/0.77          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['116', '117'])).
% 0.54/0.77  thf('119', plain,
% 0.54/0.77      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.54/0.77        | (v2_struct_0 @ sk_A))),
% 0.54/0.77      inference('clc', [status(thm)], ['113', '118'])).
% 0.54/0.77  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.77  thf('121', plain,
% 0.54/0.77      ((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 0.54/0.77      inference('clc', [status(thm)], ['119', '120'])).
% 0.54/0.77  thf('122', plain,
% 0.54/0.77      (((r1_orders_2 @ sk_A @ sk_B @ 
% 0.54/0.77         (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.54/0.77        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['95', '121'])).
% 0.54/0.77  thf('123', plain,
% 0.54/0.77      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.77         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.54/0.77          | ~ (r1_orders_2 @ X13 @ X12 @ X10))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.77  thf('124', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.54/0.77          | (zip_tseitin_0 @ 
% 0.54/0.77             (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A) @ X0 @ 
% 0.54/0.77             sk_B @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['122', '123'])).
% 0.54/0.77  thf('125', plain,
% 0.54/0.77      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.54/0.77         ((zip_tseitin_1 @ X14 @ X15 @ X16 @ X17)
% 0.54/0.77          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.77  thf('126', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.54/0.77          | (zip_tseitin_1 @ 
% 0.54/0.77             (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A) @ X0 @ 
% 0.54/0.77             sk_B @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['124', '125'])).
% 0.54/0.77  thf('127', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.54/0.77          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.54/0.77          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.54/0.77      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.54/0.77  thf('128', plain,
% 0.54/0.77      (((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.54/0.77        | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.54/0.77        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['126', '127'])).
% 0.54/0.77  thf('129', plain,
% 0.54/0.77      ((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 0.54/0.77      inference('clc', [status(thm)], ['119', '120'])).
% 0.54/0.77  thf('130', plain,
% 0.54/0.77      (((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.54/0.77        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['128', '129'])).
% 0.54/0.77  thf('131', plain,
% 0.54/0.77      ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)),
% 0.54/0.77      inference('simplify', [status(thm)], ['130'])).
% 0.54/0.77  thf('132', plain,
% 0.54/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.77         (((X20) = (k1_yellow_0 @ X18 @ X19))
% 0.54/0.77          | ~ (zip_tseitin_2 @ X19 @ X20 @ X18))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.77  thf('133', plain,
% 0.54/0.77      (((sk_B) = (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['131', '132'])).
% 0.54/0.77  thf('134', plain,
% 0.54/0.77      (((sk_B) = (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['131', '132'])).
% 0.54/0.77  thf('135', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('136', plain, ((v4_waybel_7 @ sk_B @ sk_A)),
% 0.54/0.77      inference('demod', [status(thm)], ['57', '133', '134', '135'])).
% 0.54/0.77  thf('137', plain, ($false), inference('demod', [status(thm)], ['0', '136'])).
% 0.54/0.77  
% 0.54/0.77  % SZS output end Refutation
% 0.54/0.77  
% 0.54/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
