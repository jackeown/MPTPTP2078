%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bl6NTkOJOt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:17 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 628 expanded)
%              Number of leaves         :   47 ( 200 expanded)
%              Depth                    :   21
%              Number of atoms          : 1612 (8786 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_waybel_6_type,type,(
    v5_waybel_6: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_waybel_7_type,type,(
    v4_waybel_7: $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ~ ( v1_lattice3 @ X2 )
      | ~ ( v2_struct_0 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('7',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','9'])).

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

thf('11',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ( X34
       != ( k1_yellow_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v1_waybel_7 @ X36 @ X35 )
      | ~ ( v12_waybel_0 @ X36 @ X35 )
      | ~ ( v1_waybel_0 @ X36 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ( v4_waybel_7 @ X34 @ X35 )
      | ~ ( l1_orders_2 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( l1_orders_2 @ X35 )
      | ( v4_waybel_7 @ ( k1_yellow_0 @ X35 @ X36 ) @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( v1_waybel_0 @ X36 @ X35 )
      | ~ ( v12_waybel_0 @ X36 @ X35 )
      | ~ ( v1_waybel_7 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X35 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
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
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_orders_2 @ X32 @ X33 @ X31 )
      | ( r2_hidden @ X33 @ ( k5_waybel_0 @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X0 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('28',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('31',plain,(
    r2_hidden @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_lattice3 @ X12 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_1 @ X13 @ X14 @ X15 @ X16 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_1 @ X13 @ X14 @ X15 @ X16 )
      | ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X16 ) ) ) ),
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

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_lattice3 @ X4 @ X5 @ X3 )
      | ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_orders_2 @ X4 @ X6 @ X3 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_1 @ X1 @ X5 @ X4 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_1 @ X0 @ X1 @ X4 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ X1 @ sk_A ) ) ),
    inference(condensation,[status(thm)],['43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_lattice3 @ X21 @ X24 @ X20 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X24 @ X20 @ X21 ) @ X24 @ X20 @ X21 )
      | ( zip_tseitin_2 @ X24 @ X20 @ X21 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ( r2_lattice3 @ X4 @ X5 @ X3 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ( r2_lattice3 @ X4 @ X5 @ X3 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_hidden @ X33 @ ( k5_waybel_0 @ X32 @ X31 ) )
      | ( r1_orders_2 @ X32 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ( r2_lattice3 @ X4 @ X5 @ X3 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('77',plain,(
    r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['51','77'])).

thf('79',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ~ ( r1_orders_2 @ X12 @ X11 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_1 @ X13 @ X14 @ X15 @ X16 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('84',plain,
    ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r2_lattice3 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['75','76'])).

thf('86',plain,
    ( ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    zip_tseitin_2 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X19
        = ( k1_yellow_0 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_2 @ X18 @ X19 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('89',plain,
    ( sk_B
    = ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc12_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) )).

thf('92',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( v12_waybel_0 @ ( k5_waybel_0 @ X27 @ X28 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc12_waybel_0])).

thf('93',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('98',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( v1_waybel_0 @ ( k5_waybel_0 @ X29 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('101',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('106',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( sk_B
    = ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','89','90','98','106','107','108','109','110','111','112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_xboole_0 @ ( k5_waybel_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v4_waybel_7 @ sk_B @ sk_A )
    | ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['114','122'])).

thf('124',plain,(
    ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
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

thf('127',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ( v1_waybel_7 @ ( k5_waybel_0 @ X38 @ X37 ) @ X38 )
      | ~ ( v5_waybel_6 @ X37 @ X38 )
      | ~ ( l1_orders_2 @ X38 )
      | ~ ( v2_lattice3 @ X38 )
      | ~ ( v1_lattice3 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t37_waybel_7])).

thf('128',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_6 @ sk_B @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v5_waybel_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['125','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bl6NTkOJOt
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:52:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 278 iterations in 0.219s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(v1_waybel_0_type, type, v1_waybel_0: $i > $i > $o).
% 0.49/0.68  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.49/0.68  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.49/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(v5_waybel_6_type, type, v5_waybel_6: $i > $i > $o).
% 0.49/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.68  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.49/0.68  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.49/0.68  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.49/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.49/0.68  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 0.49/0.68  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.49/0.68  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.49/0.68  thf(v12_waybel_0_type, type, v12_waybel_0: $i > $i > $o).
% 0.49/0.68  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.49/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.49/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.68  thf(v4_waybel_7_type, type, v4_waybel_7: $i > $i > $o).
% 0.49/0.68  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.49/0.68  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.49/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.68  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.49/0.68  thf(v1_waybel_7_type, type, v1_waybel_7: $i > $i > $o).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(t38_waybel_7, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.49/0.68         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68           ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.49/0.68            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68              ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t38_waybel_7])).
% 0.49/0.68  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_k5_waybel_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.49/0.68         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68       ( m1_subset_1 @
% 0.49/0.68         ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      (![X25 : $i, X26 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X25)
% 0.49/0.68          | (v2_struct_0 @ X25)
% 0.49/0.68          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.49/0.68          | (m1_subset_1 @ (k5_waybel_0 @ X25 @ X26) @ 
% 0.49/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k5_waybel_0])).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.49/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.68        | (v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (l1_orders_2 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('3', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.49/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(cc1_lattice3, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_orders_2 @ A ) =>
% 0.49/0.68       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (![X2 : $i]:
% 0.49/0.68         (~ (v1_lattice3 @ X2) | ~ (v2_struct_0 @ X2) | ~ (l1_orders_2 @ X2))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.49/0.68  thf('7', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('8', plain, ((v1_lattice3 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      ((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('clc', [status(thm)], ['4', '9'])).
% 0.49/0.68  thf(d6_waybel_7, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.49/0.68         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68           ( ( v4_waybel_7 @ B @ A ) <=>
% 0.49/0.68             ( ?[C:$i]:
% 0.49/0.68               ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.49/0.68                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.49/0.68                 ( v1_waybel_7 @ C @ A ) & ( v12_waybel_0 @ C @ A ) & 
% 0.49/0.68                 ( v1_waybel_0 @ C @ A ) & ( ~( v1_xboole_0 @ C ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 0.49/0.68          | ((X34) != (k1_yellow_0 @ X35 @ X36))
% 0.49/0.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.68          | ~ (v1_waybel_7 @ X36 @ X35)
% 0.49/0.68          | ~ (v12_waybel_0 @ X36 @ X35)
% 0.49/0.68          | ~ (v1_waybel_0 @ X36 @ X35)
% 0.49/0.68          | (v1_xboole_0 @ X36)
% 0.49/0.68          | (v4_waybel_7 @ X34 @ X35)
% 0.49/0.68          | ~ (l1_orders_2 @ X35)
% 0.49/0.68          | ~ (v2_lattice3 @ X35)
% 0.49/0.68          | ~ (v1_lattice3 @ X35)
% 0.49/0.68          | ~ (v5_orders_2 @ X35)
% 0.49/0.68          | ~ (v4_orders_2 @ X35)
% 0.49/0.68          | ~ (v3_orders_2 @ X35))),
% 0.49/0.68      inference('cnf', [status(esa)], [d6_waybel_7])).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      (![X35 : $i, X36 : $i]:
% 0.49/0.68         (~ (v3_orders_2 @ X35)
% 0.49/0.68          | ~ (v4_orders_2 @ X35)
% 0.49/0.68          | ~ (v5_orders_2 @ X35)
% 0.49/0.68          | ~ (v1_lattice3 @ X35)
% 0.49/0.68          | ~ (v2_lattice3 @ X35)
% 0.49/0.68          | ~ (l1_orders_2 @ X35)
% 0.49/0.68          | (v4_waybel_7 @ (k1_yellow_0 @ X35 @ X36) @ X35)
% 0.49/0.68          | (v1_xboole_0 @ X36)
% 0.49/0.68          | ~ (v1_waybel_0 @ X36 @ X35)
% 0.49/0.68          | ~ (v12_waybel_0 @ X36 @ X35)
% 0.49/0.68          | ~ (v1_waybel_7 @ X36 @ X35)
% 0.49/0.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_yellow_0 @ X35 @ X36) @ (u1_struct_0 @ X35)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['11'])).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      ((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.49/0.68           (u1_struct_0 @ sk_A))
% 0.49/0.68        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.68        | ~ (v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.68        | ~ (v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.68        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.49/0.68        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.49/0.68           sk_A)
% 0.49/0.68        | ~ (l1_orders_2 @ sk_A)
% 0.49/0.68        | ~ (v2_lattice3 @ sk_A)
% 0.49/0.68        | ~ (v1_lattice3 @ sk_A)
% 0.49/0.68        | ~ (v5_orders_2 @ sk_A)
% 0.49/0.68        | ~ (v4_orders_2 @ sk_A)
% 0.49/0.68        | ~ (v3_orders_2 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['10', '12'])).
% 0.49/0.68  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(t17_waybel_0, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68           ( ![C:$i]:
% 0.49/0.68             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68               ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) ) <=>
% 0.49/0.68                 ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.49/0.68          | ~ (r1_orders_2 @ X32 @ X33 @ X31)
% 0.49/0.68          | (r2_hidden @ X33 @ (k5_waybel_0 @ X32 @ X31))
% 0.49/0.68          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.49/0.68          | ~ (l1_orders_2 @ X32)
% 0.49/0.68          | (v2_struct_0 @ X32))),
% 0.49/0.68      inference('cnf', [status(esa)], [t17_waybel_0])).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (l1_orders_2 @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.49/0.68  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.49/0.68        | (r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['14', '19'])).
% 0.49/0.68  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(t24_orders_2, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.49/0.68          | (r1_orders_2 @ X1 @ X0 @ X0)
% 0.49/0.68          | ~ (l1_orders_2 @ X1)
% 0.49/0.68          | ~ (v3_orders_2 @ X1)
% 0.49/0.68          | (v2_struct_0 @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v3_orders_2 @ sk_A)
% 0.49/0.68        | ~ (l1_orders_2 @ sk_A)
% 0.49/0.68        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.68  thf('24', plain, ((v3_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.49/0.69  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.69  thf('28', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.49/0.69      inference('clc', [status(thm)], ['26', '27'])).
% 0.49/0.69  thf('29', plain,
% 0.49/0.69      (((r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['20', '28'])).
% 0.49/0.69  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.69  thf('31', plain, ((r2_hidden @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B))),
% 0.49/0.69      inference('clc', [status(thm)], ['29', '30'])).
% 0.49/0.69  thf(t30_yellow_0, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69           ( ![C:$i]:
% 0.49/0.69             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.49/0.69                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.49/0.69                 ( ( ![D:$i]:
% 0.49/0.69                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.49/0.69                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.49/0.69                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.49/0.69               ( ( ( ![D:$i]:
% 0.49/0.69                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.49/0.69                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.49/0.69                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.49/0.69                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.49/0.69                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_1, axiom,
% 0.49/0.69    (![D:$i,C:$i,B:$i,A:$i]:
% 0.49/0.69     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.49/0.69       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.49/0.69  thf('32', plain,
% 0.49/0.69      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.49/0.69         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.49/0.69          | (r2_lattice3 @ X12 @ X10 @ X9))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.69  thf(zf_stmt_2, axiom,
% 0.49/0.69    (![D:$i,C:$i,B:$i,A:$i]:
% 0.49/0.69     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.49/0.69       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.49/0.69  thf('33', plain,
% 0.49/0.69      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.69         ((zip_tseitin_1 @ X13 @ X14 @ X15 @ X16)
% 0.49/0.69          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.69  thf('34', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.69         ((r2_lattice3 @ X0 @ X2 @ X3) | (zip_tseitin_1 @ X3 @ X2 @ X1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.69  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('36', plain,
% 0.49/0.69      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.69         ((zip_tseitin_1 @ X13 @ X14 @ X15 @ X16)
% 0.49/0.69          | (m1_subset_1 @ X13 @ (u1_struct_0 @ X16)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.69  thf(d9_lattice3, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_orders_2 @ A ) =>
% 0.49/0.69       ( ![B:$i,C:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.49/0.69             ( ![D:$i]:
% 0.49/0.69               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.49/0.69  thf('37', plain,
% 0.49/0.69      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.49/0.69          | ~ (r2_lattice3 @ X4 @ X5 @ X3)
% 0.49/0.69          | ~ (r2_hidden @ X6 @ X5)
% 0.49/0.69          | (r1_orders_2 @ X4 @ X6 @ X3)
% 0.49/0.69          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.49/0.69          | ~ (l1_orders_2 @ X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.49/0.69  thf('38', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.69         ((zip_tseitin_1 @ X1 @ X5 @ X4 @ X0)
% 0.49/0.69          | ~ (l1_orders_2 @ X0)
% 0.49/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.69          | (r1_orders_2 @ X0 @ X2 @ X1)
% 0.49/0.69          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.69          | ~ (r2_lattice3 @ X0 @ X3 @ X1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.49/0.69  thf('39', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.69         (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 0.49/0.69          | ~ (r2_hidden @ sk_B @ X1)
% 0.49/0.69          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.49/0.69          | ~ (l1_orders_2 @ sk_A)
% 0.49/0.69          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['35', '38'])).
% 0.49/0.69  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('41', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.69         (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 0.49/0.69          | ~ (r2_hidden @ sk_B @ X1)
% 0.49/0.69          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.49/0.69          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['39', '40'])).
% 0.49/0.69  thf('42', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.69         ((zip_tseitin_1 @ X0 @ X1 @ X4 @ sk_A)
% 0.49/0.69          | (zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 0.49/0.69          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.49/0.69          | ~ (r2_hidden @ sk_B @ X1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['34', '41'])).
% 0.49/0.69  thf('43', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.69         ((r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.49/0.69          | (zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A)
% 0.49/0.69          | (zip_tseitin_1 @ X0 @ (k5_waybel_0 @ sk_A @ sk_B) @ X3 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['31', '42'])).
% 0.49/0.69  thf('44', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.49/0.69          | (zip_tseitin_1 @ X0 @ (k5_waybel_0 @ sk_A @ sk_B) @ X1 @ sk_A))),
% 0.49/0.69      inference('condensation', [status(thm)], ['43'])).
% 0.49/0.69  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_4, axiom,
% 0.49/0.69    (![C:$i,B:$i,A:$i]:
% 0.49/0.69     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.49/0.69       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.49/0.69  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.49/0.69  thf(zf_stmt_7, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69           ( ![C:$i]:
% 0.49/0.69             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.49/0.69                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.49/0.69                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.49/0.69               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.49/0.69                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.49/0.69                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.49/0.69                   ( ![D:$i]:
% 0.49/0.69                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.49/0.69                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.69  thf('46', plain,
% 0.49/0.69      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.49/0.69          | ~ (r2_lattice3 @ X21 @ X24 @ X20)
% 0.49/0.69          | ~ (zip_tseitin_1 @ (sk_D_1 @ X24 @ X20 @ X21) @ X24 @ X20 @ X21)
% 0.49/0.69          | (zip_tseitin_2 @ X24 @ X20 @ X21)
% 0.49/0.69          | ~ (l1_orders_2 @ X21)
% 0.49/0.69          | ~ (v5_orders_2 @ X21))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.49/0.69  thf('47', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v5_orders_2 @ sk_A)
% 0.49/0.69          | ~ (l1_orders_2 @ sk_A)
% 0.49/0.69          | (zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.49/0.69          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.49/0.69          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.49/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.69  thf('48', plain, ((v5_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('50', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.49/0.69          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.49/0.69          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.49/0.69  thf('51', plain,
% 0.49/0.69      (((r1_orders_2 @ sk_A @ sk_B @ 
% 0.49/0.69         (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.49/0.69        | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.49/0.69        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['44', '50'])).
% 0.49/0.69  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('53', plain,
% 0.49/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.49/0.69          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ (u1_struct_0 @ X4))
% 0.49/0.69          | (r2_lattice3 @ X4 @ X5 @ X3)
% 0.49/0.69          | ~ (l1_orders_2 @ X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.49/0.69  thf('54', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (l1_orders_2 @ sk_A)
% 0.49/0.69          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.49/0.69          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['52', '53'])).
% 0.49/0.69  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('56', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.49/0.69          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['54', '55'])).
% 0.49/0.69  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('58', plain,
% 0.49/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.49/0.69          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.49/0.69          | (r2_lattice3 @ X4 @ X5 @ X3)
% 0.49/0.69          | ~ (l1_orders_2 @ X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.49/0.69  thf('59', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (l1_orders_2 @ sk_A)
% 0.49/0.69          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.49/0.69          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.69  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('61', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.49/0.69          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.49/0.69      inference('demod', [status(thm)], ['59', '60'])).
% 0.49/0.69  thf('62', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('63', plain,
% 0.49/0.69      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.49/0.69          | ~ (r2_hidden @ X33 @ (k5_waybel_0 @ X32 @ X31))
% 0.49/0.69          | (r1_orders_2 @ X32 @ X33 @ X31)
% 0.49/0.69          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.49/0.69          | ~ (l1_orders_2 @ X32)
% 0.49/0.69          | (v2_struct_0 @ X32))),
% 0.49/0.69      inference('cnf', [status(esa)], [t17_waybel_0])).
% 0.49/0.69  thf('64', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((v2_struct_0 @ sk_A)
% 0.49/0.69          | ~ (l1_orders_2 @ sk_A)
% 0.49/0.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.69          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.49/0.69          | ~ (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.69  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('66', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((v2_struct_0 @ sk_A)
% 0.49/0.69          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.69          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.49/0.69          | ~ (r2_hidden @ X0 @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.69  thf('67', plain,
% 0.49/0.69      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.49/0.69        | (r1_orders_2 @ sk_A @ 
% 0.49/0.69           (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.49/0.69        | ~ (m1_subset_1 @ 
% 0.49/0.69             (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ 
% 0.49/0.69             (u1_struct_0 @ sk_A))
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['61', '66'])).
% 0.49/0.69  thf('68', plain,
% 0.49/0.69      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.49/0.69        | (v2_struct_0 @ sk_A)
% 0.49/0.69        | (r1_orders_2 @ sk_A @ 
% 0.49/0.69           (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.49/0.69        | (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B))),
% 0.49/0.69      inference('sup-', [status(thm)], ['56', '67'])).
% 0.49/0.69  thf('69', plain,
% 0.49/0.69      (((r1_orders_2 @ sk_A @ 
% 0.49/0.69         (sk_D @ sk_B @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A) @ sk_B)
% 0.49/0.69        | (v2_struct_0 @ sk_A)
% 0.49/0.69        | (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B))),
% 0.49/0.69      inference('simplify', [status(thm)], ['68'])).
% 0.49/0.69  thf('70', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('71', plain,
% 0.49/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.49/0.69          | ~ (r1_orders_2 @ X4 @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.49/0.69          | (r2_lattice3 @ X4 @ X5 @ X3)
% 0.49/0.69          | ~ (l1_orders_2 @ X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.49/0.69  thf('72', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (l1_orders_2 @ sk_A)
% 0.49/0.69          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.49/0.69          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.49/0.69      inference('sup-', [status(thm)], ['70', '71'])).
% 0.49/0.69  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('74', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.49/0.69          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.69  thf('75', plain,
% 0.49/0.69      (((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('clc', [status(thm)], ['69', '74'])).
% 0.49/0.69  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.69  thf('77', plain, ((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 0.49/0.69      inference('clc', [status(thm)], ['75', '76'])).
% 0.49/0.69  thf('78', plain,
% 0.49/0.69      (((r1_orders_2 @ sk_A @ sk_B @ 
% 0.49/0.69         (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))
% 0.49/0.69        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['51', '77'])).
% 0.49/0.69  thf('79', plain,
% 0.49/0.69      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.49/0.69         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.49/0.69          | ~ (r1_orders_2 @ X12 @ X11 @ X9))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.69  thf('80', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.49/0.69          | (zip_tseitin_0 @ 
% 0.49/0.69             (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A) @ X0 @ 
% 0.49/0.69             sk_B @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.69  thf('81', plain,
% 0.49/0.69      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.69         ((zip_tseitin_1 @ X13 @ X14 @ X15 @ X16)
% 0.49/0.69          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.69  thf('82', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.49/0.69          | (zip_tseitin_1 @ 
% 0.49/0.69             (sk_D_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A) @ X0 @ 
% 0.49/0.69             sk_B @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['80', '81'])).
% 0.49/0.69  thf('83', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((zip_tseitin_2 @ X0 @ sk_B @ sk_A)
% 0.49/0.69          | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.49/0.69          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.49/0.69  thf('84', plain,
% 0.49/0.69      (((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.49/0.69        | ~ (r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.49/0.69        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['82', '83'])).
% 0.49/0.69  thf('85', plain, ((r2_lattice3 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 0.49/0.69      inference('clc', [status(thm)], ['75', '76'])).
% 0.49/0.69  thf('86', plain,
% 0.49/0.69      (((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)
% 0.49/0.69        | (zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['84', '85'])).
% 0.49/0.69  thf('87', plain,
% 0.49/0.69      ((zip_tseitin_2 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_B @ sk_A)),
% 0.49/0.69      inference('simplify', [status(thm)], ['86'])).
% 0.49/0.69  thf('88', plain,
% 0.49/0.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.69         (((X19) = (k1_yellow_0 @ X17 @ X18))
% 0.49/0.69          | ~ (zip_tseitin_2 @ X18 @ X19 @ X17))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.49/0.69  thf('89', plain,
% 0.49/0.69      (((sk_B) = (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.49/0.69  thf('90', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('91', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(fc12_waybel_0, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_orders_2 @ A ) & 
% 0.49/0.69         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69       ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ))).
% 0.49/0.69  thf('92', plain,
% 0.49/0.69      (![X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (l1_orders_2 @ X27)
% 0.49/0.69          | ~ (v4_orders_2 @ X27)
% 0.49/0.69          | (v2_struct_0 @ X27)
% 0.49/0.69          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.49/0.69          | (v12_waybel_0 @ (k5_waybel_0 @ X27 @ X28) @ X27))),
% 0.49/0.69      inference('cnf', [status(esa)], [fc12_waybel_0])).
% 0.49/0.69  thf('93', plain,
% 0.49/0.69      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (v4_orders_2 @ sk_A)
% 0.49/0.69        | ~ (l1_orders_2 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['91', '92'])).
% 0.49/0.69  thf('94', plain, ((v4_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('96', plain,
% 0.49/0.69      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.49/0.69  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.69  thf('98', plain, ((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.49/0.69      inference('clc', [status(thm)], ['96', '97'])).
% 0.49/0.69  thf('99', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(fc8_waybel_0, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.49/0.69         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69       ( ( ~( v1_xboole_0 @ ( k5_waybel_0 @ A @ B ) ) ) & 
% 0.49/0.69         ( v1_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ))).
% 0.49/0.69  thf('100', plain,
% 0.49/0.69      (![X29 : $i, X30 : $i]:
% 0.49/0.69         (~ (l1_orders_2 @ X29)
% 0.49/0.69          | ~ (v3_orders_2 @ X29)
% 0.49/0.69          | (v2_struct_0 @ X29)
% 0.49/0.69          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.49/0.69          | (v1_waybel_0 @ (k5_waybel_0 @ X29 @ X30) @ X29))),
% 0.49/0.69      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 0.49/0.69  thf('101', plain,
% 0.49/0.69      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (v3_orders_2 @ sk_A)
% 0.49/0.69        | ~ (l1_orders_2 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['99', '100'])).
% 0.49/0.69  thf('102', plain, ((v3_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('103', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('104', plain,
% 0.49/0.69      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.69        | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.49/0.69  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.69  thf('106', plain, ((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.49/0.69      inference('clc', [status(thm)], ['104', '105'])).
% 0.49/0.69  thf('107', plain,
% 0.49/0.69      (((sk_B) = (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.49/0.69  thf('108', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('109', plain, ((v2_lattice3 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('110', plain, ((v1_lattice3 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('111', plain, ((v5_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('112', plain, ((v4_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('113', plain, ((v3_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('114', plain,
% 0.49/0.69      ((~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.49/0.69        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.49/0.69        | (v4_waybel_7 @ sk_B @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)],
% 0.49/0.69                ['13', '89', '90', '98', '106', '107', '108', '109', '110', 
% 0.49/0.69                 '111', '112', '113'])).
% 0.49/0.69  thf('115', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('116', plain,
% 0.49/0.69      (![X29 : $i, X30 : $i]:
% 0.49/0.69         (~ (l1_orders_2 @ X29)
% 0.49/0.69          | ~ (v3_orders_2 @ X29)
% 0.49/0.69          | (v2_struct_0 @ X29)
% 0.49/0.69          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.49/0.69          | ~ (v1_xboole_0 @ (k5_waybel_0 @ X29 @ X30)))),
% 0.49/0.69      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 0.49/0.69  thf('117', plain,
% 0.49/0.69      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.49/0.69        | (v2_struct_0 @ sk_A)
% 0.49/0.69        | ~ (v3_orders_2 @ sk_A)
% 0.49/0.69        | ~ (l1_orders_2 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.69  thf('118', plain, ((v3_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('119', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('120', plain,
% 0.49/0.69      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.49/0.69  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.69  thf('122', plain, (~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))),
% 0.49/0.69      inference('clc', [status(thm)], ['120', '121'])).
% 0.49/0.69  thf('123', plain,
% 0.49/0.69      (((v4_waybel_7 @ sk_B @ sk_A)
% 0.49/0.69        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 0.49/0.69      inference('clc', [status(thm)], ['114', '122'])).
% 0.49/0.69  thf('124', plain, (~ (v4_waybel_7 @ sk_B @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('125', plain, (~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.49/0.69      inference('clc', [status(thm)], ['123', '124'])).
% 0.49/0.69  thf('126', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(t37_waybel_7, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.49/0.69         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.69           ( ( v5_waybel_6 @ B @ A ) =>
% 0.49/0.69             ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.49/0.69  thf('127', plain,
% 0.49/0.69      (![X37 : $i, X38 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 0.49/0.69          | (v1_waybel_7 @ (k5_waybel_0 @ X38 @ X37) @ X38)
% 0.49/0.69          | ~ (v5_waybel_6 @ X37 @ X38)
% 0.49/0.69          | ~ (l1_orders_2 @ X38)
% 0.49/0.69          | ~ (v2_lattice3 @ X38)
% 0.49/0.69          | ~ (v1_lattice3 @ X38)
% 0.49/0.69          | ~ (v5_orders_2 @ X38)
% 0.49/0.69          | ~ (v4_orders_2 @ X38)
% 0.49/0.69          | ~ (v3_orders_2 @ X38))),
% 0.49/0.69      inference('cnf', [status(esa)], [t37_waybel_7])).
% 0.49/0.69  thf('128', plain,
% 0.49/0.69      ((~ (v3_orders_2 @ sk_A)
% 0.49/0.69        | ~ (v4_orders_2 @ sk_A)
% 0.49/0.69        | ~ (v5_orders_2 @ sk_A)
% 0.49/0.69        | ~ (v1_lattice3 @ sk_A)
% 0.49/0.69        | ~ (v2_lattice3 @ sk_A)
% 0.49/0.69        | ~ (l1_orders_2 @ sk_A)
% 0.49/0.69        | ~ (v5_waybel_6 @ sk_B @ sk_A)
% 0.49/0.69        | (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['126', '127'])).
% 0.49/0.69  thf('129', plain, ((v3_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('130', plain, ((v4_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('131', plain, ((v5_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('132', plain, ((v1_lattice3 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('133', plain, ((v2_lattice3 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('134', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('135', plain, ((v5_waybel_6 @ sk_B @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('136', plain, ((v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.49/0.69      inference('demod', [status(thm)],
% 0.49/0.69                ['128', '129', '130', '131', '132', '133', '134', '135'])).
% 0.49/0.69  thf('137', plain, ($false), inference('demod', [status(thm)], ['125', '136'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
