%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tt3922UN5y

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:13 EST 2020

% Result     : Theorem 6.06s
% Output     : Refutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 405 expanded)
%              Number of leaves         :   42 ( 134 expanded)
%              Depth                    :   27
%              Number of atoms          : 1308 (5766 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t8_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
            <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_7])).

thf('0',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k3_yellow_0 @ X19 )
        = ( k1_yellow_0 @ X19 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X26: $i] :
      ( ( r1_yellow_0 @ X26 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v1_yellow_0 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X3 @ X4 ) @ X4 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('6',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X17 @ X16 ) @ X17 )
      | ( r2_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_subset_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k2_subset_1 @ X0 ) @ X0 ) @ ( k2_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_subset_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 = X31 )
      | ( v1_subset_1 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( k2_subset_1 @ X0 ) @ X0 )
      | ( ( k2_subset_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_subset_1 @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_subset_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_subset_1 @ X32 @ X31 )
      | ( X32 != X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('26',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_subset_1 @ X31 @ X31 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ~ ( v1_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_subset_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,
    ( ( k2_subset_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['10','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k1_yellow_0 @ X20 @ X21 ) )
      | ~ ( r2_lattice3 @ X20 @ X21 @ X23 )
      | ( r1_orders_2 @ X20 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_yellow_0 @ X20 @ X21 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( r1_yellow_0 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r1_orders_2 @ X20 @ ( k1_yellow_0 @ X20 @ X21 ) @ X23 )
      | ~ ( r2_lattice3 @ X20 @ X21 @ X23 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','48'])).

thf('50',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup+',[status(thm)],['2','55'])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('61',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d20_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( r1_orders_2 @ X28 @ X30 @ X29 )
      | ~ ( r2_hidden @ X30 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','72'])).

thf('74',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('75',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X3 @ X4 ) @ X3 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('77',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','82'])).

thf('84',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['79'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_subset_1 @ X31 @ X31 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('88',plain,
    ( ~ ( v1_subset_1 @ sk_B @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['81'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 = X31 )
      | ( v1_subset_1 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('93',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X19: $i] :
      ( ( ( k3_yellow_0 @ X19 )
        = ( k1_yellow_0 @ X19 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('97',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('100',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['95','101'])).

thf('103',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('104',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['81'])).

thf('109',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','89','90','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tt3922UN5y
% 0.13/0.37  % Computer   : n003.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:12:57 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 6.06/6.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.06/6.25  % Solved by: fo/fo7.sh
% 6.06/6.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.06/6.25  % done 7315 iterations in 5.767s
% 6.06/6.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.06/6.25  % SZS output start Refutation
% 6.06/6.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.06/6.25  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 6.06/6.25  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.06/6.25  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 6.06/6.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.06/6.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.06/6.25  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 6.06/6.25  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 6.06/6.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.06/6.25  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 6.06/6.25  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 6.06/6.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.06/6.25  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 6.06/6.25  thf(sk_A_type, type, sk_A: $i).
% 6.06/6.25  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 6.06/6.25  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 6.06/6.25  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 6.06/6.25  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 6.06/6.25  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 6.06/6.25  thf(sk_B_type, type, sk_B: $i).
% 6.06/6.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.06/6.25  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 6.06/6.25  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.06/6.25  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 6.06/6.25  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 6.06/6.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.06/6.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.06/6.25  thf(t8_waybel_7, conjecture,
% 6.06/6.25    (![A:$i]:
% 6.06/6.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.06/6.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 6.06/6.25         ( l1_orders_2 @ A ) ) =>
% 6.06/6.25       ( ![B:$i]:
% 6.06/6.25         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 6.06/6.25             ( v13_waybel_0 @ B @ A ) & 
% 6.06/6.25             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.06/6.25           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 6.06/6.25             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 6.06/6.25  thf(zf_stmt_0, negated_conjecture,
% 6.06/6.25    (~( ![A:$i]:
% 6.06/6.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.06/6.25            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 6.06/6.25            ( l1_orders_2 @ A ) ) =>
% 6.06/6.25          ( ![B:$i]:
% 6.06/6.25            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 6.06/6.25                ( v13_waybel_0 @ B @ A ) & 
% 6.06/6.25                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.06/6.25              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 6.06/6.25                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 6.06/6.25    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 6.06/6.25  thf('0', plain,
% 6.06/6.25      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 6.06/6.25        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('1', plain,
% 6.06/6.25      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 6.06/6.25       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('split', [status(esa)], ['0'])).
% 6.06/6.25  thf(d11_yellow_0, axiom,
% 6.06/6.25    (![A:$i]:
% 6.06/6.25     ( ( l1_orders_2 @ A ) =>
% 6.06/6.25       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 6.06/6.25  thf('2', plain,
% 6.06/6.25      (![X19 : $i]:
% 6.06/6.25         (((k3_yellow_0 @ X19) = (k1_yellow_0 @ X19 @ k1_xboole_0))
% 6.06/6.25          | ~ (l1_orders_2 @ X19))),
% 6.06/6.25      inference('cnf', [status(esa)], [d11_yellow_0])).
% 6.06/6.25  thf(t42_yellow_0, axiom,
% 6.06/6.25    (![A:$i]:
% 6.06/6.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 6.06/6.25         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 6.06/6.25       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 6.06/6.25         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 6.06/6.25  thf('3', plain,
% 6.06/6.25      (![X26 : $i]:
% 6.06/6.25         ((r1_yellow_0 @ X26 @ k1_xboole_0)
% 6.06/6.25          | ~ (l1_orders_2 @ X26)
% 6.06/6.25          | ~ (v1_yellow_0 @ X26)
% 6.06/6.25          | ~ (v5_orders_2 @ X26)
% 6.06/6.25          | (v2_struct_0 @ X26))),
% 6.06/6.25      inference('cnf', [status(esa)], [t42_yellow_0])).
% 6.06/6.25  thf('4', plain,
% 6.06/6.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf(t49_subset_1, axiom,
% 6.06/6.25    (![A:$i,B:$i]:
% 6.06/6.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.06/6.25       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 6.06/6.25         ( ( A ) = ( B ) ) ) ))).
% 6.06/6.25  thf('5', plain,
% 6.06/6.25      (![X3 : $i, X4 : $i]:
% 6.06/6.25         ((m1_subset_1 @ (sk_C_1 @ X3 @ X4) @ X4)
% 6.06/6.25          | ((X4) = (X3))
% 6.06/6.25          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 6.06/6.25      inference('cnf', [status(esa)], [t49_subset_1])).
% 6.06/6.25  thf('6', plain,
% 6.06/6.25      ((((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25        | (m1_subset_1 @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 6.06/6.25           (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['4', '5'])).
% 6.06/6.25  thf(d9_lattice3, axiom,
% 6.06/6.25    (![A:$i]:
% 6.06/6.25     ( ( l1_orders_2 @ A ) =>
% 6.06/6.25       ( ![B:$i,C:$i]:
% 6.06/6.25         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.06/6.25           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 6.06/6.25             ( ![D:$i]:
% 6.06/6.25               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.06/6.25                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 6.06/6.25  thf('7', plain,
% 6.06/6.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.06/6.25         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 6.06/6.25          | (r2_hidden @ (sk_D @ X15 @ X17 @ X16) @ X17)
% 6.06/6.25          | (r2_lattice3 @ X16 @ X17 @ X15)
% 6.06/6.25          | ~ (l1_orders_2 @ X16))),
% 6.06/6.25      inference('cnf', [status(esa)], [d9_lattice3])).
% 6.06/6.25  thf('8', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25          | ~ (l1_orders_2 @ sk_A)
% 6.06/6.25          | (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25          | (r2_hidden @ 
% 6.06/6.25             (sk_D @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0 @ sk_A) @ X0))),
% 6.06/6.25      inference('sup-', [status(thm)], ['6', '7'])).
% 6.06/6.25  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('10', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25          | (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25          | (r2_hidden @ 
% 6.06/6.25             (sk_D @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0 @ sk_A) @ X0))),
% 6.06/6.25      inference('demod', [status(thm)], ['8', '9'])).
% 6.06/6.25  thf(dt_k2_subset_1, axiom,
% 6.06/6.25    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 6.06/6.25  thf('11', plain,
% 6.06/6.25      (![X0 : $i]: (m1_subset_1 @ (k2_subset_1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 6.06/6.25      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 6.06/6.25  thf(t10_subset_1, axiom,
% 6.06/6.25    (![A:$i,B:$i]:
% 6.06/6.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.06/6.25       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 6.06/6.25            ( ![C:$i]:
% 6.06/6.25              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 6.06/6.25  thf('12', plain,
% 6.06/6.25      (![X1 : $i, X2 : $i]:
% 6.06/6.25         ((r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 6.06/6.25          | ((X1) = (k1_xboole_0))
% 6.06/6.25          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 6.06/6.25      inference('cnf', [status(esa)], [t10_subset_1])).
% 6.06/6.25  thf('13', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (((k2_subset_1 @ X0) = (k1_xboole_0))
% 6.06/6.25          | (r2_hidden @ (sk_C @ (k2_subset_1 @ X0) @ X0) @ (k2_subset_1 @ X0)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['11', '12'])).
% 6.06/6.25  thf('14', plain,
% 6.06/6.25      (![X0 : $i]: (m1_subset_1 @ (k2_subset_1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 6.06/6.25      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 6.06/6.25  thf(t5_subset, axiom,
% 6.06/6.25    (![A:$i,B:$i,C:$i]:
% 6.06/6.25     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 6.06/6.25          ( v1_xboole_0 @ C ) ) ))).
% 6.06/6.25  thf('15', plain,
% 6.06/6.25      (![X12 : $i, X13 : $i, X14 : $i]:
% 6.06/6.25         (~ (r2_hidden @ X12 @ X13)
% 6.06/6.25          | ~ (v1_xboole_0 @ X14)
% 6.06/6.25          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 6.06/6.25      inference('cnf', [status(esa)], [t5_subset])).
% 6.06/6.25  thf('16', plain,
% 6.06/6.25      (![X0 : $i, X1 : $i]:
% 6.06/6.25         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k2_subset_1 @ X0)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['14', '15'])).
% 6.06/6.25  thf('17', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (((k2_subset_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.06/6.25      inference('sup-', [status(thm)], ['13', '16'])).
% 6.06/6.25  thf('18', plain,
% 6.06/6.25      (![X0 : $i]: (m1_subset_1 @ (k2_subset_1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 6.06/6.25      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 6.06/6.25  thf(d7_subset_1, axiom,
% 6.06/6.25    (![A:$i,B:$i]:
% 6.06/6.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.06/6.25       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 6.06/6.25  thf('19', plain,
% 6.06/6.25      (![X31 : $i, X32 : $i]:
% 6.06/6.25         (((X32) = (X31))
% 6.06/6.25          | (v1_subset_1 @ X32 @ X31)
% 6.06/6.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 6.06/6.25      inference('cnf', [status(esa)], [d7_subset_1])).
% 6.06/6.25  thf('20', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         ((v1_subset_1 @ (k2_subset_1 @ X0) @ X0) | ((k2_subset_1 @ X0) = (X0)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['18', '19'])).
% 6.06/6.25  thf('21', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         ((v1_subset_1 @ k1_xboole_0 @ X0)
% 6.06/6.25          | ~ (v1_xboole_0 @ X0)
% 6.06/6.25          | ((k2_subset_1 @ X0) = (X0)))),
% 6.06/6.25      inference('sup+', [status(thm)], ['17', '20'])).
% 6.06/6.25  thf('22', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (((k2_subset_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.06/6.25      inference('sup-', [status(thm)], ['13', '16'])).
% 6.06/6.25  thf('23', plain,
% 6.06/6.25      (![X0 : $i]: (m1_subset_1 @ (k2_subset_1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 6.06/6.25      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 6.06/6.25  thf('24', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 6.06/6.25          | ~ (v1_xboole_0 @ X0))),
% 6.06/6.25      inference('sup+', [status(thm)], ['22', '23'])).
% 6.06/6.25  thf('25', plain,
% 6.06/6.25      (![X31 : $i, X32 : $i]:
% 6.06/6.25         (~ (v1_subset_1 @ X32 @ X31)
% 6.06/6.25          | ((X32) != (X31))
% 6.06/6.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 6.06/6.25      inference('cnf', [status(esa)], [d7_subset_1])).
% 6.06/6.25  thf('26', plain,
% 6.06/6.25      (![X31 : $i]:
% 6.06/6.25         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X31))
% 6.06/6.25          | ~ (v1_subset_1 @ X31 @ X31))),
% 6.06/6.25      inference('simplify', [status(thm)], ['25'])).
% 6.06/6.25  thf('27', plain,
% 6.06/6.25      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.06/6.25        | ~ (v1_subset_1 @ k1_xboole_0 @ k1_xboole_0))),
% 6.06/6.25      inference('sup-', [status(thm)], ['24', '26'])).
% 6.06/6.25  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.06/6.25  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.06/6.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.06/6.25  thf('29', plain, (~ (v1_subset_1 @ k1_xboole_0 @ k1_xboole_0)),
% 6.06/6.25      inference('demod', [status(thm)], ['27', '28'])).
% 6.06/6.25  thf('30', plain,
% 6.06/6.25      ((((k2_subset_1 @ k1_xboole_0) = (k1_xboole_0))
% 6.06/6.25        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.06/6.25      inference('sup-', [status(thm)], ['21', '29'])).
% 6.06/6.25  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.06/6.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.06/6.25  thf('32', plain, (((k2_subset_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.06/6.25      inference('demod', [status(thm)], ['30', '31'])).
% 6.06/6.25  thf('33', plain,
% 6.06/6.25      (![X0 : $i, X1 : $i]:
% 6.06/6.25         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k2_subset_1 @ X0)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['14', '15'])).
% 6.06/6.25  thf('34', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.06/6.25      inference('sup-', [status(thm)], ['32', '33'])).
% 6.06/6.25  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.06/6.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.06/6.25  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.06/6.25      inference('demod', [status(thm)], ['34', '35'])).
% 6.06/6.25  thf('37', plain,
% 6.06/6.25      (((r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 6.06/6.25         (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['10', '36'])).
% 6.06/6.25  thf('38', plain,
% 6.06/6.25      ((((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25        | (m1_subset_1 @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 6.06/6.25           (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['4', '5'])).
% 6.06/6.25  thf(dt_k1_yellow_0, axiom,
% 6.06/6.25    (![A:$i,B:$i]:
% 6.06/6.25     ( ( l1_orders_2 @ A ) =>
% 6.06/6.25       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 6.06/6.25  thf('39', plain,
% 6.06/6.25      (![X24 : $i, X25 : $i]:
% 6.06/6.25         (~ (l1_orders_2 @ X24)
% 6.06/6.25          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 6.06/6.25      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 6.06/6.25  thf(d9_yellow_0, axiom,
% 6.06/6.25    (![A:$i]:
% 6.06/6.25     ( ( l1_orders_2 @ A ) =>
% 6.06/6.25       ( ![B:$i,C:$i]:
% 6.06/6.25         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.06/6.25           ( ( r1_yellow_0 @ A @ B ) =>
% 6.06/6.25             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 6.06/6.25               ( ( r2_lattice3 @ A @ B @ C ) & 
% 6.06/6.25                 ( ![D:$i]:
% 6.06/6.25                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.06/6.25                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 6.06/6.25                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 6.06/6.25  thf('40', plain,
% 6.06/6.25      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 6.06/6.25         (((X22) != (k1_yellow_0 @ X20 @ X21))
% 6.06/6.25          | ~ (r2_lattice3 @ X20 @ X21 @ X23)
% 6.06/6.25          | (r1_orders_2 @ X20 @ X22 @ X23)
% 6.06/6.25          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 6.06/6.25          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 6.06/6.25          | ~ (r1_yellow_0 @ X20 @ X21)
% 6.06/6.25          | ~ (l1_orders_2 @ X20))),
% 6.06/6.25      inference('cnf', [status(esa)], [d9_yellow_0])).
% 6.06/6.25  thf('41', plain,
% 6.06/6.25      (![X20 : $i, X21 : $i, X23 : $i]:
% 6.06/6.25         (~ (l1_orders_2 @ X20)
% 6.06/6.25          | ~ (r1_yellow_0 @ X20 @ X21)
% 6.06/6.25          | ~ (m1_subset_1 @ (k1_yellow_0 @ X20 @ X21) @ (u1_struct_0 @ X20))
% 6.06/6.25          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 6.06/6.25          | (r1_orders_2 @ X20 @ (k1_yellow_0 @ X20 @ X21) @ X23)
% 6.06/6.25          | ~ (r2_lattice3 @ X20 @ X21 @ X23))),
% 6.06/6.25      inference('simplify', [status(thm)], ['40'])).
% 6.06/6.25  thf('42', plain,
% 6.06/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.06/6.25         (~ (l1_orders_2 @ X0)
% 6.06/6.25          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 6.06/6.25          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 6.06/6.25          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 6.06/6.25          | ~ (r1_yellow_0 @ X0 @ X1)
% 6.06/6.25          | ~ (l1_orders_2 @ X0))),
% 6.06/6.25      inference('sup-', [status(thm)], ['39', '41'])).
% 6.06/6.25  thf('43', plain,
% 6.06/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.06/6.25         (~ (r1_yellow_0 @ X0 @ X1)
% 6.06/6.25          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 6.06/6.25          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 6.06/6.25          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 6.06/6.25          | ~ (l1_orders_2 @ X0))),
% 6.06/6.25      inference('simplify', [status(thm)], ['42'])).
% 6.06/6.25  thf('44', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25          | ~ (l1_orders_2 @ sk_A)
% 6.06/6.25          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 6.06/6.25             (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 6.06/6.25      inference('sup-', [status(thm)], ['38', '43'])).
% 6.06/6.25  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('46', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 6.06/6.25             (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 6.06/6.25      inference('demod', [status(thm)], ['44', '45'])).
% 6.06/6.25  thf('47', plain,
% 6.06/6.25      ((((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 6.06/6.25        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 6.06/6.25           (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['37', '46'])).
% 6.06/6.25  thf('48', plain,
% 6.06/6.25      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 6.06/6.25         (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 6.06/6.25        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 6.06/6.25      inference('simplify', [status(thm)], ['47'])).
% 6.06/6.25  thf('49', plain,
% 6.06/6.25      (((v2_struct_0 @ sk_A)
% 6.06/6.25        | ~ (v5_orders_2 @ sk_A)
% 6.06/6.25        | ~ (v1_yellow_0 @ sk_A)
% 6.06/6.25        | ~ (l1_orders_2 @ sk_A)
% 6.06/6.25        | ((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 6.06/6.25           (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('sup-', [status(thm)], ['3', '48'])).
% 6.06/6.25  thf('50', plain, ((v5_orders_2 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('51', plain, ((v1_yellow_0 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('53', plain,
% 6.06/6.25      (((v2_struct_0 @ sk_A)
% 6.06/6.25        | ((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 6.06/6.25           (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 6.06/6.25  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('55', plain,
% 6.06/6.25      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 6.06/6.25         (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 6.06/6.25      inference('clc', [status(thm)], ['53', '54'])).
% 6.06/6.25  thf('56', plain,
% 6.06/6.25      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 6.06/6.25         (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25        | ~ (l1_orders_2 @ sk_A)
% 6.06/6.25        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 6.06/6.25      inference('sup+', [status(thm)], ['2', '55'])).
% 6.06/6.25  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('58', plain,
% 6.06/6.25      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 6.06/6.25         (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 6.06/6.25      inference('demod', [status(thm)], ['56', '57'])).
% 6.06/6.25  thf('59', plain,
% 6.06/6.25      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('split', [status(esa)], ['0'])).
% 6.06/6.25  thf('60', plain,
% 6.06/6.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf(t4_subset, axiom,
% 6.06/6.25    (![A:$i,B:$i,C:$i]:
% 6.06/6.25     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 6.06/6.25       ( m1_subset_1 @ A @ C ) ))).
% 6.06/6.25  thf('61', plain,
% 6.06/6.25      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.06/6.25         (~ (r2_hidden @ X9 @ X10)
% 6.06/6.25          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 6.06/6.25          | (m1_subset_1 @ X9 @ X11))),
% 6.06/6.25      inference('cnf', [status(esa)], [t4_subset])).
% 6.06/6.25  thf('62', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 6.06/6.25      inference('sup-', [status(thm)], ['60', '61'])).
% 6.06/6.25  thf('63', plain,
% 6.06/6.25      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['59', '62'])).
% 6.06/6.25  thf('64', plain,
% 6.06/6.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf(d20_waybel_0, axiom,
% 6.06/6.25    (![A:$i]:
% 6.06/6.25     ( ( l1_orders_2 @ A ) =>
% 6.06/6.25       ( ![B:$i]:
% 6.06/6.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.06/6.25           ( ( v13_waybel_0 @ B @ A ) <=>
% 6.06/6.25             ( ![C:$i]:
% 6.06/6.25               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.06/6.25                 ( ![D:$i]:
% 6.06/6.25                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.06/6.25                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 6.06/6.25                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 6.06/6.25  thf('65', plain,
% 6.06/6.25      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 6.06/6.25         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 6.06/6.25          | ~ (v13_waybel_0 @ X27 @ X28)
% 6.06/6.25          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 6.06/6.25          | (r2_hidden @ X29 @ X27)
% 6.06/6.25          | ~ (r1_orders_2 @ X28 @ X30 @ X29)
% 6.06/6.25          | ~ (r2_hidden @ X30 @ X27)
% 6.06/6.25          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 6.06/6.25          | ~ (l1_orders_2 @ X28))),
% 6.06/6.25      inference('cnf', [status(esa)], [d20_waybel_0])).
% 6.06/6.25  thf('66', plain,
% 6.06/6.25      (![X0 : $i, X1 : $i]:
% 6.06/6.25         (~ (l1_orders_2 @ sk_A)
% 6.06/6.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.06/6.25          | ~ (r2_hidden @ X0 @ sk_B)
% 6.06/6.25          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 6.06/6.25          | (r2_hidden @ X1 @ sk_B)
% 6.06/6.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 6.06/6.25          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 6.06/6.25      inference('sup-', [status(thm)], ['64', '65'])).
% 6.06/6.25  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('68', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('69', plain,
% 6.06/6.25      (![X0 : $i, X1 : $i]:
% 6.06/6.25         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.06/6.25          | ~ (r2_hidden @ X0 @ sk_B)
% 6.06/6.25          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 6.06/6.25          | (r2_hidden @ X1 @ sk_B)
% 6.06/6.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.06/6.25  thf('70', plain,
% 6.06/6.25      ((![X0 : $i]:
% 6.06/6.25          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.06/6.25           | (r2_hidden @ X0 @ sk_B)
% 6.06/6.25           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 6.06/6.25           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['63', '69'])).
% 6.06/6.25  thf('71', plain,
% 6.06/6.25      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('split', [status(esa)], ['0'])).
% 6.06/6.25  thf('72', plain,
% 6.06/6.25      ((![X0 : $i]:
% 6.06/6.25          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.06/6.25           | (r2_hidden @ X0 @ sk_B)
% 6.06/6.25           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('demod', [status(thm)], ['70', '71'])).
% 6.06/6.25  thf('73', plain,
% 6.06/6.25      (((((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25         | (r2_hidden @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 6.06/6.25         | ~ (m1_subset_1 @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 6.06/6.25              (u1_struct_0 @ sk_A))))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['58', '72'])).
% 6.06/6.25  thf('74', plain,
% 6.06/6.25      ((((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25        | (m1_subset_1 @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 6.06/6.25           (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['4', '5'])).
% 6.06/6.25  thf('75', plain,
% 6.06/6.25      ((((r2_hidden @ (sk_C_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 6.06/6.25         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('clc', [status(thm)], ['73', '74'])).
% 6.06/6.25  thf('76', plain,
% 6.06/6.25      (![X3 : $i, X4 : $i]:
% 6.06/6.25         (~ (r2_hidden @ (sk_C_1 @ X3 @ X4) @ X3)
% 6.06/6.25          | ((X4) = (X3))
% 6.06/6.25          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 6.06/6.25      inference('cnf', [status(esa)], [t49_subset_1])).
% 6.06/6.25  thf('77', plain,
% 6.06/6.25      (((((u1_struct_0 @ sk_A) = (sk_B))
% 6.06/6.25         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.06/6.25         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['75', '76'])).
% 6.06/6.25  thf('78', plain,
% 6.06/6.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('79', plain,
% 6.06/6.25      (((((u1_struct_0 @ sk_A) = (sk_B)) | ((u1_struct_0 @ sk_A) = (sk_B))))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('demod', [status(thm)], ['77', '78'])).
% 6.06/6.25  thf('80', plain,
% 6.06/6.25      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('simplify', [status(thm)], ['79'])).
% 6.06/6.25  thf('81', plain,
% 6.06/6.25      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 6.06/6.25        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('82', plain,
% 6.06/6.25      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('split', [status(esa)], ['81'])).
% 6.06/6.25  thf('83', plain,
% 6.06/6.25      (((v1_subset_1 @ sk_B @ sk_B))
% 6.06/6.25         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 6.06/6.25             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('sup+', [status(thm)], ['80', '82'])).
% 6.06/6.25  thf('84', plain,
% 6.06/6.25      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('simplify', [status(thm)], ['79'])).
% 6.06/6.25  thf('85', plain,
% 6.06/6.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('86', plain,
% 6.06/6.25      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B)))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('sup+', [status(thm)], ['84', '85'])).
% 6.06/6.25  thf('87', plain,
% 6.06/6.25      (![X31 : $i]:
% 6.06/6.25         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X31))
% 6.06/6.25          | ~ (v1_subset_1 @ X31 @ X31))),
% 6.06/6.25      inference('simplify', [status(thm)], ['25'])).
% 6.06/6.25  thf('88', plain,
% 6.06/6.25      ((~ (v1_subset_1 @ sk_B @ sk_B))
% 6.06/6.25         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['86', '87'])).
% 6.06/6.25  thf('89', plain,
% 6.06/6.25      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 6.06/6.25       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['83', '88'])).
% 6.06/6.25  thf('90', plain,
% 6.06/6.25      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 6.06/6.25       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('split', [status(esa)], ['81'])).
% 6.06/6.25  thf('91', plain,
% 6.06/6.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('92', plain,
% 6.06/6.25      (![X31 : $i, X32 : $i]:
% 6.06/6.25         (((X32) = (X31))
% 6.06/6.25          | (v1_subset_1 @ X32 @ X31)
% 6.06/6.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 6.06/6.25      inference('cnf', [status(esa)], [d7_subset_1])).
% 6.06/6.25  thf('93', plain,
% 6.06/6.25      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 6.06/6.25        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['91', '92'])).
% 6.06/6.25  thf('94', plain,
% 6.06/6.25      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 6.06/6.25         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('split', [status(esa)], ['0'])).
% 6.06/6.25  thf('95', plain,
% 6.06/6.25      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 6.06/6.25         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('sup-', [status(thm)], ['93', '94'])).
% 6.06/6.25  thf('96', plain,
% 6.06/6.25      (![X19 : $i]:
% 6.06/6.25         (((k3_yellow_0 @ X19) = (k1_yellow_0 @ X19 @ k1_xboole_0))
% 6.06/6.25          | ~ (l1_orders_2 @ X19))),
% 6.06/6.25      inference('cnf', [status(esa)], [d11_yellow_0])).
% 6.06/6.25  thf('97', plain,
% 6.06/6.25      (![X24 : $i, X25 : $i]:
% 6.06/6.25         (~ (l1_orders_2 @ X24)
% 6.06/6.25          | (m1_subset_1 @ (k1_yellow_0 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 6.06/6.25      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 6.06/6.25  thf('98', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         ((m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 6.06/6.25          | ~ (l1_orders_2 @ X0)
% 6.06/6.25          | ~ (l1_orders_2 @ X0))),
% 6.06/6.25      inference('sup+', [status(thm)], ['96', '97'])).
% 6.06/6.25  thf('99', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (~ (l1_orders_2 @ X0)
% 6.06/6.25          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 6.06/6.25      inference('simplify', [status(thm)], ['98'])).
% 6.06/6.25  thf(t2_subset, axiom,
% 6.06/6.25    (![A:$i,B:$i]:
% 6.06/6.25     ( ( m1_subset_1 @ A @ B ) =>
% 6.06/6.25       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 6.06/6.25  thf('100', plain,
% 6.06/6.25      (![X7 : $i, X8 : $i]:
% 6.06/6.25         ((r2_hidden @ X7 @ X8)
% 6.06/6.25          | (v1_xboole_0 @ X8)
% 6.06/6.25          | ~ (m1_subset_1 @ X7 @ X8))),
% 6.06/6.25      inference('cnf', [status(esa)], [t2_subset])).
% 6.06/6.25  thf('101', plain,
% 6.06/6.25      (![X0 : $i]:
% 6.06/6.25         (~ (l1_orders_2 @ X0)
% 6.06/6.25          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 6.06/6.25          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['99', '100'])).
% 6.06/6.25  thf('102', plain,
% 6.06/6.25      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 6.06/6.25         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 6.06/6.25         | ~ (l1_orders_2 @ sk_A)))
% 6.06/6.25         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('sup+', [status(thm)], ['95', '101'])).
% 6.06/6.25  thf('103', plain,
% 6.06/6.25      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 6.06/6.25         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('sup-', [status(thm)], ['93', '94'])).
% 6.06/6.25  thf('104', plain, ((l1_orders_2 @ sk_A)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('105', plain,
% 6.06/6.25      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 6.06/6.25         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('demod', [status(thm)], ['102', '103', '104'])).
% 6.06/6.25  thf('106', plain, (~ (v1_xboole_0 @ sk_B)),
% 6.06/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.06/6.25  thf('107', plain,
% 6.06/6.25      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 6.06/6.25         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 6.06/6.25      inference('clc', [status(thm)], ['105', '106'])).
% 6.06/6.25  thf('108', plain,
% 6.06/6.25      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 6.06/6.25         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 6.06/6.25      inference('split', [status(esa)], ['81'])).
% 6.06/6.25  thf('109', plain,
% 6.06/6.25      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 6.06/6.25       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 6.06/6.25      inference('sup-', [status(thm)], ['107', '108'])).
% 6.06/6.25  thf('110', plain, ($false),
% 6.06/6.25      inference('sat_resolution*', [status(thm)], ['1', '89', '90', '109'])).
% 6.06/6.25  
% 6.06/6.25  % SZS output end Refutation
% 6.06/6.25  
% 6.06/6.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
