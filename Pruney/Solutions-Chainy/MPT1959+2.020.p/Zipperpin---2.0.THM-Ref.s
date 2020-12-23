%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TXhpaVncnX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:11 EST 2020

% Result     : Theorem 3.33s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  226 (1163 expanded)
%              Number of leaves         :   49 ( 338 expanded)
%              Depth                    :   35
%              Number of atoms          : 2662 (19822 expanded)
%              Number of equality atoms :   42 ( 174 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( ( k3_yellow_0 @ X14 )
        = ( k1_yellow_0 @ X14 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
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
    ! [X33: $i] :
      ( ( r1_yellow_0 @ X33 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X33 )
      | ~ ( v1_yellow_0 @ X33 )
      | ~ ( v5_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('4',plain,(
    ! [X14: $i] :
      ( ( ( k3_yellow_0 @ X14 )
        = ( k1_yellow_0 @ X14 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k3_yellow_0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_lattice3 @ X20 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('17',plain,(
    ! [X28: $i,X29: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_lattice3 @ X29 @ X32 @ X28 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X32 @ X28 @ X29 ) @ X32 @ X28 @ X29 )
      | ( zip_tseitin_2 @ X32 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ X1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ X1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k3_yellow_0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X23 @ X24 )
      | ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( X28
       != ( k1_yellow_0 @ X29 @ X30 ) )
      | ~ ( r1_yellow_0 @ X29 @ X30 )
      | ~ ( r2_lattice3 @ X29 @ X30 @ X31 )
      | ( r1_orders_2 @ X29 @ X28 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('31',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v5_orders_2 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( r1_orders_2 @ X29 @ ( k1_yellow_0 @ X29 @ X30 ) @ X31 )
      | ~ ( r2_lattice3 @ X29 @ X30 @ X31 )
      | ~ ( r1_yellow_0 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( v5_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( sk_D_1 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( v5_orders_2 @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( sk_D_1 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( sk_D_1 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( sk_D_1 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_D_1 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_D_1 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 ) @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_1 @ ( sk_D_1 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) @ X0 ) @ X1 @ ( k3_yellow_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X28: $i,X29: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_lattice3 @ X29 @ X32 @ X28 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X32 @ X28 @ X29 ) @ X32 @ X28 @ X29 )
      | ( zip_tseitin_2 @ X32 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( zip_tseitin_2 @ X0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
        | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ ( k3_yellow_0 @ sk_A ) @ sk_A ) @ X0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_2 @ X0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
        | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ ( k3_yellow_0 @ sk_A ) @ sk_A ) @ X0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X12 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( k3_yellow_0 @ sk_A ) )
        | ( m1_subset_1 @ ( sk_D @ ( k3_yellow_0 @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ X0 @ ( k3_yellow_0 @ sk_A ) )
        | ( m1_subset_1 @ ( sk_D @ ( k3_yellow_0 @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('68',plain,(
    ! [X14: $i] :
      ( ( ( k3_yellow_0 @ X14 )
        = ( k1_yellow_0 @ X14 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('69',plain,(
    ! [X33: $i] :
      ( ( r1_yellow_0 @ X33 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X33 )
      | ~ ( v1_yellow_0 @ X33 )
      | ~ ( v5_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('70',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('71',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( X28
       != ( k1_yellow_0 @ X29 @ X30 ) )
      | ~ ( r1_yellow_0 @ X29 @ X30 )
      | ( r2_lattice3 @ X29 @ X30 @ X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('72',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v5_orders_2 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ( r2_lattice3 @ X29 @ X30 @ ( k1_yellow_0 @ X29 @ X30 ) )
      | ~ ( r1_yellow_0 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_orders_2 @ X11 @ X13 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X2 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v1_yellow_0 @ X1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k3_yellow_0 @ X0 ) @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ ( sk_D @ ( k3_yellow_0 @ X0 ) @ k1_xboole_0 @ X0 ) @ ( k3_yellow_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','84'])).

thf('86',plain,
    ( ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_yellow_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','85'])).

thf('87',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_yellow_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_yellow_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_yellow_0 @ sk_A ) @ k1_xboole_0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('96',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ ( sk_D @ X10 @ X12 @ X11 ) @ X10 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( k3_yellow_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_yellow_0 @ sk_A ) @ X0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ X0 @ ( k3_yellow_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_yellow_0 @ sk_A ) @ X0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['94','99'])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59','60','61','100'])).

thf('102',plain,
    ( ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_yellow_0 @ X25 @ X26 )
      | ~ ( zip_tseitin_2 @ X26 @ X27 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('106',plain,
    ( ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('108',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X3 @ X4 ) @ X4 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('109',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['115','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['106','123'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('126',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_yellow_0 @ sk_A ) @ sk_A )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('127',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X27
        = ( k1_yellow_0 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_2 @ X26 @ X27 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('128',plain,
    ( ( ( k3_yellow_0 @ sk_A )
      = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['124','125','128'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('131',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('132',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v13_waybel_0 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( r1_orders_2 @ X35 @ X37 @ X36 )
      | ~ ( r2_hidden @ X37 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_orders_2 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['130','136'])).

thf('138',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['129','139'])).

thf('141',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('142',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('144',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['148'])).

thf('150',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['147','149'])).

thf('151',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('152',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('154',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_subset_1 @ X39 @ X38 )
      | ( X39 != X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('155',plain,(
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( v1_subset_1 @ X38 @ X38 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['153','155'])).

thf('157',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','156'])).

thf('158',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['148'])).

thf('159',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 = X38 )
      | ( v1_subset_1 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('161',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('163',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('165',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['163','166'])).

thf('168',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('169',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['148'])).

thf('174',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','157','158','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TXhpaVncnX
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.33/3.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.33/3.56  % Solved by: fo/fo7.sh
% 3.33/3.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.33/3.56  % done 3002 iterations in 3.108s
% 3.33/3.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.33/3.56  % SZS output start Refutation
% 3.33/3.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.33/3.56  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 3.33/3.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 3.33/3.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.33/3.56  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 3.33/3.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.33/3.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.33/3.56  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 3.33/3.56  thf(sk_A_type, type, sk_A: $i).
% 3.33/3.56  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 3.33/3.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.33/3.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.33/3.56  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 3.33/3.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 3.33/3.56  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 3.33/3.56  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 3.33/3.56  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 3.33/3.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 3.33/3.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.33/3.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.33/3.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 3.33/3.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.33/3.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 3.33/3.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 3.33/3.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.33/3.56  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 3.33/3.56  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 3.33/3.56  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 3.33/3.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 3.33/3.56  thf(t8_waybel_7, conjecture,
% 3.33/3.56    (![A:$i]:
% 3.33/3.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.33/3.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 3.33/3.56         ( l1_orders_2 @ A ) ) =>
% 3.33/3.56       ( ![B:$i]:
% 3.33/3.56         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 3.33/3.56             ( v13_waybel_0 @ B @ A ) & 
% 3.33/3.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.33/3.56           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 3.33/3.56             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 3.33/3.56  thf(zf_stmt_0, negated_conjecture,
% 3.33/3.56    (~( ![A:$i]:
% 3.33/3.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.33/3.56            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 3.33/3.56            ( l1_orders_2 @ A ) ) =>
% 3.33/3.56          ( ![B:$i]:
% 3.33/3.56            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 3.33/3.56                ( v13_waybel_0 @ B @ A ) & 
% 3.33/3.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.33/3.56              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 3.33/3.56                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 3.33/3.56    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 3.33/3.56  thf('0', plain,
% 3.33/3.56      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 3.33/3.56        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('1', plain,
% 3.33/3.56      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 3.33/3.56       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('split', [status(esa)], ['0'])).
% 3.33/3.56  thf(d11_yellow_0, axiom,
% 3.33/3.56    (![A:$i]:
% 3.33/3.56     ( ( l1_orders_2 @ A ) =>
% 3.33/3.56       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 3.33/3.56  thf('2', plain,
% 3.33/3.56      (![X14 : $i]:
% 3.33/3.56         (((k3_yellow_0 @ X14) = (k1_yellow_0 @ X14 @ k1_xboole_0))
% 3.33/3.56          | ~ (l1_orders_2 @ X14))),
% 3.33/3.56      inference('cnf', [status(esa)], [d11_yellow_0])).
% 3.33/3.56  thf(t42_yellow_0, axiom,
% 3.33/3.56    (![A:$i]:
% 3.33/3.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 3.33/3.56         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.33/3.56       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 3.33/3.56         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 3.33/3.56  thf('3', plain,
% 3.33/3.56      (![X33 : $i]:
% 3.33/3.56         ((r1_yellow_0 @ X33 @ k1_xboole_0)
% 3.33/3.56          | ~ (l1_orders_2 @ X33)
% 3.33/3.56          | ~ (v1_yellow_0 @ X33)
% 3.33/3.56          | ~ (v5_orders_2 @ X33)
% 3.33/3.56          | (v2_struct_0 @ X33))),
% 3.33/3.56      inference('cnf', [status(esa)], [t42_yellow_0])).
% 3.33/3.56  thf('4', plain,
% 3.33/3.56      (![X14 : $i]:
% 3.33/3.56         (((k3_yellow_0 @ X14) = (k1_yellow_0 @ X14 @ k1_xboole_0))
% 3.33/3.56          | ~ (l1_orders_2 @ X14))),
% 3.33/3.56      inference('cnf', [status(esa)], [d11_yellow_0])).
% 3.33/3.56  thf(dt_k1_yellow_0, axiom,
% 3.33/3.56    (![A:$i,B:$i]:
% 3.33/3.56     ( ( l1_orders_2 @ A ) =>
% 3.33/3.56       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 3.33/3.56  thf('5', plain,
% 3.33/3.56      (![X15 : $i, X16 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X15)
% 3.33/3.56          | (m1_subset_1 @ (k1_yellow_0 @ X15 @ X16) @ (u1_struct_0 @ X15)))),
% 3.33/3.56      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 3.33/3.56  thf('6', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('sup+', [status(thm)], ['4', '5'])).
% 3.33/3.56  thf('7', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['6'])).
% 3.33/3.56  thf(d9_lattice3, axiom,
% 3.33/3.56    (![A:$i]:
% 3.33/3.56     ( ( l1_orders_2 @ A ) =>
% 3.33/3.56       ( ![B:$i,C:$i]:
% 3.33/3.56         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 3.33/3.56             ( ![D:$i]:
% 3.33/3.56               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 3.33/3.56  thf('8', plain,
% 3.33/3.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 3.33/3.56          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 3.33/3.56          | (r2_lattice3 @ X11 @ X12 @ X10)
% 3.33/3.56          | ~ (l1_orders_2 @ X11))),
% 3.33/3.56      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.33/3.56  thf('9', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | (r2_hidden @ (sk_D @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1))),
% 3.33/3.56      inference('sup-', [status(thm)], ['7', '8'])).
% 3.33/3.56  thf('10', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         ((r2_hidden @ (sk_D @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1)
% 3.33/3.56          | (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['9'])).
% 3.33/3.56  thf(d1_xboole_0, axiom,
% 3.33/3.56    (![A:$i]:
% 3.33/3.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.33/3.56  thf('11', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.33/3.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.33/3.56  thf('12', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X1)
% 3.33/3.56          | (r2_lattice3 @ X1 @ X0 @ (k3_yellow_0 @ X1))
% 3.33/3.56          | ~ (v1_xboole_0 @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['10', '11'])).
% 3.33/3.56  thf(t30_yellow_0, axiom,
% 3.33/3.56    (![A:$i]:
% 3.33/3.56     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 3.33/3.56       ( ![B:$i]:
% 3.33/3.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56           ( ![C:$i]:
% 3.33/3.56             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 3.33/3.56                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 3.33/3.56                 ( ( ![D:$i]:
% 3.33/3.56                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 3.33/3.56                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 3.33/3.56                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 3.33/3.56               ( ( ( ![D:$i]:
% 3.33/3.56                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 3.33/3.56                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 3.33/3.56                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 3.33/3.56                 ( ( r1_yellow_0 @ A @ C ) & 
% 3.33/3.56                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 3.33/3.56  thf(zf_stmt_1, axiom,
% 3.33/3.56    (![D:$i,C:$i,B:$i,A:$i]:
% 3.33/3.56     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 3.33/3.56       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 3.33/3.56  thf('13', plain,
% 3.33/3.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.33/3.56         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 3.33/3.56          | (r2_lattice3 @ X20 @ X18 @ X17))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.33/3.56  thf(zf_stmt_2, axiom,
% 3.33/3.56    (![D:$i,C:$i,B:$i,A:$i]:
% 3.33/3.56     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 3.33/3.56       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 3.33/3.56  thf('14', plain,
% 3.33/3.56      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.33/3.56         ((zip_tseitin_1 @ X21 @ X22 @ X23 @ X24)
% 3.33/3.56          | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.33/3.56  thf('15', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.33/3.56         ((r2_lattice3 @ X0 @ X2 @ X3) | (zip_tseitin_1 @ X3 @ X2 @ X1 @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['13', '14'])).
% 3.33/3.56  thf('16', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['6'])).
% 3.33/3.56  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 3.33/3.56  thf(zf_stmt_4, axiom,
% 3.33/3.56    (![C:$i,B:$i,A:$i]:
% 3.33/3.56     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 3.33/3.56       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 3.33/3.56  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 3.33/3.56  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 3.33/3.56  thf(zf_stmt_7, axiom,
% 3.33/3.56    (![A:$i]:
% 3.33/3.56     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.33/3.56       ( ![B:$i]:
% 3.33/3.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56           ( ![C:$i]:
% 3.33/3.56             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 3.33/3.56                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 3.33/3.56                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 3.33/3.56               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 3.33/3.56                   ( r1_yellow_0 @ A @ C ) ) =>
% 3.33/3.56                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 3.33/3.56                   ( ![D:$i]:
% 3.33/3.56                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 3.33/3.56                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 3.33/3.56  thf('17', plain,
% 3.33/3.56      (![X28 : $i, X29 : $i, X32 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 3.33/3.56          | ~ (r2_lattice3 @ X29 @ X32 @ X28)
% 3.33/3.56          | ~ (zip_tseitin_1 @ (sk_D_1 @ X32 @ X28 @ X29) @ X32 @ X28 @ X29)
% 3.33/3.56          | (zip_tseitin_2 @ X32 @ X28 @ X29)
% 3.33/3.56          | ~ (l1_orders_2 @ X29)
% 3.33/3.56          | ~ (v5_orders_2 @ X29))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.33/3.56  thf('18', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (zip_tseitin_1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0) @ X1 @ 
% 3.33/3.56               (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['16', '17'])).
% 3.33/3.56  thf('19', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (zip_tseitin_1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0) @ X1 @ 
% 3.33/3.56               (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['18'])).
% 3.33/3.56  thf('20', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         ((r2_lattice3 @ X0 @ X1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['15', '19'])).
% 3.33/3.56  thf('21', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (v1_xboole_0 @ X1)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (r2_lattice3 @ X0 @ X1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['12', '20'])).
% 3.33/3.56  thf('22', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         ((r2_lattice3 @ X0 @ X1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_xboole_0 @ X1))),
% 3.33/3.56      inference('simplify', [status(thm)], ['21'])).
% 3.33/3.56  thf('23', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X1)
% 3.33/3.56          | (r2_lattice3 @ X1 @ X0 @ (k3_yellow_0 @ X1))
% 3.33/3.56          | ~ (v1_xboole_0 @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['10', '11'])).
% 3.33/3.56  thf('24', plain,
% 3.33/3.56      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.33/3.56         ((zip_tseitin_1 @ X21 @ X22 @ X23 @ X24)
% 3.33/3.56          | (m1_subset_1 @ X21 @ (u1_struct_0 @ X24)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.33/3.56  thf('25', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (zip_tseitin_1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0) @ X1 @ 
% 3.33/3.56               (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['18'])).
% 3.33/3.56  thf('26', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         ((m1_subset_1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0) @ 
% 3.33/3.56           (u1_struct_0 @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['24', '25'])).
% 3.33/3.56  thf('27', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (v1_xboole_0 @ X1)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (m1_subset_1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0) @ 
% 3.33/3.56             (u1_struct_0 @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['23', '26'])).
% 3.33/3.56  thf('28', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         ((m1_subset_1 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0) @ 
% 3.33/3.56           (u1_struct_0 @ X0))
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_xboole_0 @ X1))),
% 3.33/3.56      inference('simplify', [status(thm)], ['27'])).
% 3.33/3.56  thf('29', plain,
% 3.33/3.56      (![X15 : $i, X16 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X15)
% 3.33/3.56          | (m1_subset_1 @ (k1_yellow_0 @ X15 @ X16) @ (u1_struct_0 @ X15)))),
% 3.33/3.56      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 3.33/3.56  thf('30', plain,
% 3.33/3.56      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 3.33/3.56          | ((X28) != (k1_yellow_0 @ X29 @ X30))
% 3.33/3.56          | ~ (r1_yellow_0 @ X29 @ X30)
% 3.33/3.56          | ~ (r2_lattice3 @ X29 @ X30 @ X31)
% 3.33/3.56          | (r1_orders_2 @ X29 @ X28 @ X31)
% 3.33/3.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 3.33/3.56          | ~ (l1_orders_2 @ X29)
% 3.33/3.56          | ~ (v5_orders_2 @ X29))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.33/3.56  thf('31', plain,
% 3.33/3.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.33/3.56         (~ (v5_orders_2 @ X29)
% 3.33/3.56          | ~ (l1_orders_2 @ X29)
% 3.33/3.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 3.33/3.56          | (r1_orders_2 @ X29 @ (k1_yellow_0 @ X29 @ X30) @ X31)
% 3.33/3.56          | ~ (r2_lattice3 @ X29 @ X30 @ X31)
% 3.33/3.56          | ~ (r1_yellow_0 @ X29 @ X30)
% 3.33/3.56          | ~ (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['30'])).
% 3.33/3.56  thf('32', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X1)
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 3.33/3.56          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 3.33/3.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['29', '31'])).
% 3.33/3.56  thf('33', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.56         (~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.33/3.56          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X1)
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['32'])).
% 3.33/3.56  thf('34', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.56         (~ (v1_xboole_0 @ X1)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X2)
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X2 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 3.33/3.56             (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | ~ (v5_orders_2 @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['28', '33'])).
% 3.33/3.56  thf('35', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.56         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 3.33/3.56           (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X2 @ (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X2)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_xboole_0 @ X1))),
% 3.33/3.56      inference('simplify', [status(thm)], ['34'])).
% 3.33/3.56  thf('36', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (v1_xboole_0 @ X1)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_xboole_0 @ X1)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X1)
% 3.33/3.56          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 3.33/3.56             (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['22', '35'])).
% 3.33/3.56  thf('37', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 3.33/3.56           (sk_D_1 @ X1 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X1)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ X1 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_xboole_0 @ X1))),
% 3.33/3.56      inference('simplify', [status(thm)], ['36'])).
% 3.33/3.56  thf('38', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((v2_struct_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.33/3.56             (sk_D_1 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['3', '37'])).
% 3.33/3.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.33/3.56  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.33/3.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.33/3.56  thf('40', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((v2_struct_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.33/3.56             (sk_D_1 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)))),
% 3.33/3.56      inference('demod', [status(thm)], ['38', '39'])).
% 3.33/3.56  thf('41', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.33/3.56           (sk_D_1 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['40'])).
% 3.33/3.56  thf('42', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 3.33/3.56           (sk_D_1 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0))),
% 3.33/3.56      inference('sup+', [status(thm)], ['2', '41'])).
% 3.33/3.56  thf('43', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 3.33/3.56             (sk_D_1 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['42'])).
% 3.33/3.56  thf('44', plain,
% 3.33/3.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.33/3.56         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 3.33/3.56          | ~ (r1_orders_2 @ X20 @ X19 @ X17))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.33/3.56  thf('45', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | (zip_tseitin_0 @ 
% 3.33/3.56             (sk_D_1 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0) @ X1 @ 
% 3.33/3.56             (k3_yellow_0 @ X0) @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['43', '44'])).
% 3.33/3.56  thf('46', plain,
% 3.33/3.56      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.33/3.56         ((zip_tseitin_1 @ X21 @ X22 @ X23 @ X24)
% 3.33/3.56          | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.33/3.56  thf('47', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         ((zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (zip_tseitin_1 @ 
% 3.33/3.56             (sk_D_1 @ k1_xboole_0 @ (k3_yellow_0 @ X0) @ X0) @ X1 @ 
% 3.33/3.56             (k3_yellow_0 @ X0) @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['45', '46'])).
% 3.33/3.56  thf('48', plain,
% 3.33/3.56      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('split', [status(esa)], ['0'])).
% 3.33/3.56  thf('49', plain,
% 3.33/3.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf(t4_subset, axiom,
% 3.33/3.56    (![A:$i,B:$i,C:$i]:
% 3.33/3.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 3.33/3.56       ( m1_subset_1 @ A @ C ) ))).
% 3.33/3.56  thf('50', plain,
% 3.33/3.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.33/3.56         (~ (r2_hidden @ X7 @ X8)
% 3.33/3.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 3.33/3.56          | (m1_subset_1 @ X7 @ X9))),
% 3.33/3.56      inference('cnf', [status(esa)], [t4_subset])).
% 3.33/3.56  thf('51', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.33/3.56          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.33/3.56      inference('sup-', [status(thm)], ['49', '50'])).
% 3.33/3.56  thf('52', plain,
% 3.33/3.56      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['48', '51'])).
% 3.33/3.56  thf('53', plain,
% 3.33/3.56      (![X28 : $i, X29 : $i, X32 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 3.33/3.56          | ~ (r2_lattice3 @ X29 @ X32 @ X28)
% 3.33/3.56          | ~ (zip_tseitin_1 @ (sk_D_1 @ X32 @ X28 @ X29) @ X32 @ X28 @ X29)
% 3.33/3.56          | (zip_tseitin_2 @ X32 @ X28 @ X29)
% 3.33/3.56          | ~ (l1_orders_2 @ X29)
% 3.33/3.56          | ~ (v5_orders_2 @ X29))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.33/3.56  thf('54', plain,
% 3.33/3.56      ((![X0 : $i]:
% 3.33/3.56          (~ (v5_orders_2 @ sk_A)
% 3.33/3.56           | ~ (l1_orders_2 @ sk_A)
% 3.33/3.56           | (zip_tseitin_2 @ X0 @ (k3_yellow_0 @ sk_A) @ sk_A)
% 3.33/3.56           | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ (k3_yellow_0 @ sk_A) @ sk_A) @ 
% 3.33/3.56                X0 @ (k3_yellow_0 @ sk_A) @ sk_A)
% 3.33/3.56           | ~ (r2_lattice3 @ sk_A @ X0 @ (k3_yellow_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['52', '53'])).
% 3.33/3.56  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('57', plain,
% 3.33/3.56      ((![X0 : $i]:
% 3.33/3.56          ((zip_tseitin_2 @ X0 @ (k3_yellow_0 @ sk_A) @ sk_A)
% 3.33/3.56           | ~ (zip_tseitin_1 @ (sk_D_1 @ X0 @ (k3_yellow_0 @ sk_A) @ sk_A) @ 
% 3.33/3.56                X0 @ (k3_yellow_0 @ sk_A) @ sk_A)
% 3.33/3.56           | ~ (r2_lattice3 @ sk_A @ X0 @ (k3_yellow_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('demod', [status(thm)], ['54', '55', '56'])).
% 3.33/3.56  thf('58', plain,
% 3.33/3.56      (((~ (l1_orders_2 @ sk_A)
% 3.33/3.56         | (v2_struct_0 @ sk_A)
% 3.33/3.56         | ~ (v5_orders_2 @ sk_A)
% 3.33/3.56         | ~ (v1_yellow_0 @ sk_A)
% 3.33/3.56         | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ sk_A) @ sk_A)
% 3.33/3.56         | ~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56         | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ sk_A) @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['47', '57'])).
% 3.33/3.56  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('60', plain, ((v5_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('61', plain, ((v1_yellow_0 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('62', plain,
% 3.33/3.56      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['48', '51'])).
% 3.33/3.56  thf('63', plain,
% 3.33/3.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 3.33/3.56          | (m1_subset_1 @ (sk_D @ X10 @ X12 @ X11) @ (u1_struct_0 @ X11))
% 3.33/3.56          | (r2_lattice3 @ X11 @ X12 @ X10)
% 3.33/3.56          | ~ (l1_orders_2 @ X11))),
% 3.33/3.56      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.33/3.56  thf('64', plain,
% 3.33/3.56      ((![X0 : $i]:
% 3.33/3.56          (~ (l1_orders_2 @ sk_A)
% 3.33/3.56           | (r2_lattice3 @ sk_A @ X0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56           | (m1_subset_1 @ (sk_D @ (k3_yellow_0 @ sk_A) @ X0 @ sk_A) @ 
% 3.33/3.56              (u1_struct_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['62', '63'])).
% 3.33/3.56  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('66', plain,
% 3.33/3.56      ((![X0 : $i]:
% 3.33/3.56          ((r2_lattice3 @ sk_A @ X0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56           | (m1_subset_1 @ (sk_D @ (k3_yellow_0 @ sk_A) @ X0 @ sk_A) @ 
% 3.33/3.56              (u1_struct_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('demod', [status(thm)], ['64', '65'])).
% 3.33/3.56  thf('67', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         ((r2_hidden @ (sk_D @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1)
% 3.33/3.56          | (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['9'])).
% 3.33/3.56  thf('68', plain,
% 3.33/3.56      (![X14 : $i]:
% 3.33/3.56         (((k3_yellow_0 @ X14) = (k1_yellow_0 @ X14 @ k1_xboole_0))
% 3.33/3.56          | ~ (l1_orders_2 @ X14))),
% 3.33/3.56      inference('cnf', [status(esa)], [d11_yellow_0])).
% 3.33/3.56  thf('69', plain,
% 3.33/3.56      (![X33 : $i]:
% 3.33/3.56         ((r1_yellow_0 @ X33 @ k1_xboole_0)
% 3.33/3.56          | ~ (l1_orders_2 @ X33)
% 3.33/3.56          | ~ (v1_yellow_0 @ X33)
% 3.33/3.56          | ~ (v5_orders_2 @ X33)
% 3.33/3.56          | (v2_struct_0 @ X33))),
% 3.33/3.56      inference('cnf', [status(esa)], [t42_yellow_0])).
% 3.33/3.56  thf('70', plain,
% 3.33/3.56      (![X15 : $i, X16 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X15)
% 3.33/3.56          | (m1_subset_1 @ (k1_yellow_0 @ X15 @ X16) @ (u1_struct_0 @ X15)))),
% 3.33/3.56      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 3.33/3.56  thf('71', plain,
% 3.33/3.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 3.33/3.56          | ((X28) != (k1_yellow_0 @ X29 @ X30))
% 3.33/3.56          | ~ (r1_yellow_0 @ X29 @ X30)
% 3.33/3.56          | (r2_lattice3 @ X29 @ X30 @ X28)
% 3.33/3.56          | ~ (l1_orders_2 @ X29)
% 3.33/3.56          | ~ (v5_orders_2 @ X29))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 3.33/3.56  thf('72', plain,
% 3.33/3.56      (![X29 : $i, X30 : $i]:
% 3.33/3.56         (~ (v5_orders_2 @ X29)
% 3.33/3.56          | ~ (l1_orders_2 @ X29)
% 3.33/3.56          | (r2_lattice3 @ X29 @ X30 @ (k1_yellow_0 @ X29 @ X30))
% 3.33/3.56          | ~ (r1_yellow_0 @ X29 @ X30)
% 3.33/3.56          | ~ (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['71'])).
% 3.33/3.56  thf('73', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X1)
% 3.33/3.56          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['70', '72'])).
% 3.33/3.56  thf('74', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (v5_orders_2 @ X0)
% 3.33/3.56          | (r2_lattice3 @ X0 @ X1 @ (k1_yellow_0 @ X0 @ X1))
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X1)
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['73'])).
% 3.33/3.56  thf('75', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((v2_struct_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ k1_xboole_0))
% 3.33/3.56          | ~ (v5_orders_2 @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['69', '74'])).
% 3.33/3.56  thf('76', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ k1_xboole_0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['75'])).
% 3.33/3.56  thf('77', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('sup+', [status(thm)], ['68', '76'])).
% 3.33/3.56  thf('78', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (k3_yellow_0 @ X0)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['77'])).
% 3.33/3.56  thf('79', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['6'])).
% 3.33/3.56  thf('80', plain,
% 3.33/3.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 3.33/3.56          | ~ (r2_lattice3 @ X11 @ X12 @ X10)
% 3.33/3.56          | ~ (r2_hidden @ X13 @ X12)
% 3.33/3.56          | (r1_orders_2 @ X11 @ X13 @ X10)
% 3.33/3.56          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 3.33/3.56          | ~ (l1_orders_2 @ X11))),
% 3.33/3.56      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.33/3.56  thf('81', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.33/3.56          | (r1_orders_2 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (r2_hidden @ X1 @ X2)
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X2 @ (k3_yellow_0 @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['79', '80'])).
% 3.33/3.56  thf('82', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.56         (~ (r2_lattice3 @ X0 @ X2 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (r2_hidden @ X1 @ X2)
% 3.33/3.56          | (r1_orders_2 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['81'])).
% 3.33/3.56  thf('83', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0)
% 3.33/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.33/3.56          | (r1_orders_2 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['78', '82'])).
% 3.33/3.56  thf('84', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 3.33/3.56          | (r1_orders_2 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.33/3.56          | ~ (v1_yellow_0 @ X0)
% 3.33/3.56          | ~ (v5_orders_2 @ X0)
% 3.33/3.56          | (v2_struct_0 @ X0)
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['83'])).
% 3.33/3.56  thf('85', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (k3_yellow_0 @ X0))
% 3.33/3.56          | ~ (l1_orders_2 @ X1)
% 3.33/3.56          | (v2_struct_0 @ X1)
% 3.33/3.56          | ~ (v5_orders_2 @ X1)
% 3.33/3.56          | ~ (v1_yellow_0 @ X1)
% 3.33/3.56          | ~ (m1_subset_1 @ (sk_D @ (k3_yellow_0 @ X0) @ k1_xboole_0 @ X0) @ 
% 3.33/3.56               (u1_struct_0 @ X1))
% 3.33/3.56          | (r1_orders_2 @ X1 @ 
% 3.33/3.56             (sk_D @ (k3_yellow_0 @ X0) @ k1_xboole_0 @ X0) @ 
% 3.33/3.56             (k3_yellow_0 @ X1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['67', '84'])).
% 3.33/3.56  thf('86', plain,
% 3.33/3.56      ((((r2_lattice3 @ sk_A @ k1_xboole_0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56         | (r1_orders_2 @ sk_A @ 
% 3.33/3.56            (sk_D @ (k3_yellow_0 @ sk_A) @ k1_xboole_0 @ sk_A) @ 
% 3.33/3.56            (k3_yellow_0 @ sk_A))
% 3.33/3.56         | ~ (v1_yellow_0 @ sk_A)
% 3.33/3.56         | ~ (v5_orders_2 @ sk_A)
% 3.33/3.56         | (v2_struct_0 @ sk_A)
% 3.33/3.56         | ~ (l1_orders_2 @ sk_A)
% 3.33/3.56         | (r2_lattice3 @ sk_A @ k1_xboole_0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56         | ~ (l1_orders_2 @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['66', '85'])).
% 3.33/3.56  thf('87', plain, ((v1_yellow_0 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('90', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('91', plain,
% 3.33/3.56      ((((r2_lattice3 @ sk_A @ k1_xboole_0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56         | (r1_orders_2 @ sk_A @ 
% 3.33/3.56            (sk_D @ (k3_yellow_0 @ sk_A) @ k1_xboole_0 @ sk_A) @ 
% 3.33/3.56            (k3_yellow_0 @ sk_A))
% 3.33/3.56         | (v2_struct_0 @ sk_A)
% 3.33/3.56         | (r2_lattice3 @ sk_A @ k1_xboole_0 @ (k3_yellow_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 3.33/3.56  thf('92', plain,
% 3.33/3.56      ((((v2_struct_0 @ sk_A)
% 3.33/3.56         | (r1_orders_2 @ sk_A @ 
% 3.33/3.56            (sk_D @ (k3_yellow_0 @ sk_A) @ k1_xboole_0 @ sk_A) @ 
% 3.33/3.56            (k3_yellow_0 @ sk_A))
% 3.33/3.56         | (r2_lattice3 @ sk_A @ k1_xboole_0 @ (k3_yellow_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['91'])).
% 3.33/3.56  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('94', plain,
% 3.33/3.56      ((((r2_lattice3 @ sk_A @ k1_xboole_0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56         | (r1_orders_2 @ sk_A @ 
% 3.33/3.56            (sk_D @ (k3_yellow_0 @ sk_A) @ k1_xboole_0 @ sk_A) @ 
% 3.33/3.56            (k3_yellow_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('clc', [status(thm)], ['92', '93'])).
% 3.33/3.56  thf('95', plain,
% 3.33/3.56      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['48', '51'])).
% 3.33/3.56  thf('96', plain,
% 3.33/3.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 3.33/3.56          | ~ (r1_orders_2 @ X11 @ (sk_D @ X10 @ X12 @ X11) @ X10)
% 3.33/3.56          | (r2_lattice3 @ X11 @ X12 @ X10)
% 3.33/3.56          | ~ (l1_orders_2 @ X11))),
% 3.33/3.56      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.33/3.56  thf('97', plain,
% 3.33/3.56      ((![X0 : $i]:
% 3.33/3.56          (~ (l1_orders_2 @ sk_A)
% 3.33/3.56           | (r2_lattice3 @ sk_A @ X0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56           | ~ (r1_orders_2 @ sk_A @ 
% 3.33/3.56                (sk_D @ (k3_yellow_0 @ sk_A) @ X0 @ sk_A) @ 
% 3.33/3.56                (k3_yellow_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['95', '96'])).
% 3.33/3.56  thf('98', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('99', plain,
% 3.33/3.56      ((![X0 : $i]:
% 3.33/3.56          ((r2_lattice3 @ sk_A @ X0 @ (k3_yellow_0 @ sk_A))
% 3.33/3.56           | ~ (r1_orders_2 @ sk_A @ 
% 3.33/3.56                (sk_D @ (k3_yellow_0 @ sk_A) @ X0 @ sk_A) @ 
% 3.33/3.56                (k3_yellow_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('demod', [status(thm)], ['97', '98'])).
% 3.33/3.56  thf('100', plain,
% 3.33/3.56      (((r2_lattice3 @ sk_A @ k1_xboole_0 @ (k3_yellow_0 @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('clc', [status(thm)], ['94', '99'])).
% 3.33/3.56  thf('101', plain,
% 3.33/3.56      ((((v2_struct_0 @ sk_A)
% 3.33/3.56         | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ sk_A) @ sk_A)
% 3.33/3.56         | (zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ sk_A) @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('demod', [status(thm)], ['58', '59', '60', '61', '100'])).
% 3.33/3.56  thf('102', plain,
% 3.33/3.56      ((((zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ sk_A) @ sk_A)
% 3.33/3.56         | (v2_struct_0 @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['101'])).
% 3.33/3.56  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('104', plain,
% 3.33/3.56      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ sk_A) @ sk_A))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('clc', [status(thm)], ['102', '103'])).
% 3.33/3.56  thf('105', plain,
% 3.33/3.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.33/3.56         ((r1_yellow_0 @ X25 @ X26) | ~ (zip_tseitin_2 @ X26 @ X27 @ X25))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.33/3.56  thf('106', plain,
% 3.33/3.56      (((r1_yellow_0 @ sk_A @ k1_xboole_0))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['104', '105'])).
% 3.33/3.56  thf('107', plain,
% 3.33/3.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf(t49_subset_1, axiom,
% 3.33/3.56    (![A:$i,B:$i]:
% 3.33/3.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.33/3.56       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 3.33/3.56         ( ( A ) = ( B ) ) ) ))).
% 3.33/3.56  thf('108', plain,
% 3.33/3.56      (![X3 : $i, X4 : $i]:
% 3.33/3.56         ((m1_subset_1 @ (sk_C @ X3 @ X4) @ X4)
% 3.33/3.56          | ((X4) = (X3))
% 3.33/3.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 3.33/3.56      inference('cnf', [status(esa)], [t49_subset_1])).
% 3.33/3.56  thf('109', plain,
% 3.33/3.56      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.33/3.56           (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['107', '108'])).
% 3.33/3.56  thf('110', plain,
% 3.33/3.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 3.33/3.56          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 3.33/3.56          | (r2_lattice3 @ X11 @ X12 @ X10)
% 3.33/3.56          | ~ (l1_orders_2 @ X11))),
% 3.33/3.56      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.33/3.56  thf('111', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56          | ~ (l1_orders_2 @ sk_A)
% 3.33/3.56          | (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56          | (r2_hidden @ 
% 3.33/3.56             (sk_D @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_A) @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['109', '110'])).
% 3.33/3.56  thf('112', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('113', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56          | (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56          | (r2_hidden @ 
% 3.33/3.56             (sk_D @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_A) @ X0))),
% 3.33/3.56      inference('demod', [status(thm)], ['111', '112'])).
% 3.33/3.56  thf('114', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.33/3.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.33/3.56  thf('115', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         ((r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56          | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56          | ~ (v1_xboole_0 @ X0))),
% 3.33/3.56      inference('sup-', [status(thm)], ['113', '114'])).
% 3.33/3.56  thf('116', plain,
% 3.33/3.56      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.33/3.56           (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['107', '108'])).
% 3.33/3.56  thf('117', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.56         (~ (v5_orders_2 @ X0)
% 3.33/3.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.33/3.56          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 3.33/3.56          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 3.33/3.56          | ~ (r1_yellow_0 @ X0 @ X1)
% 3.33/3.56          | ~ (l1_orders_2 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['32'])).
% 3.33/3.56  thf('118', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56          | ~ (l1_orders_2 @ sk_A)
% 3.33/3.56          | ~ (r1_yellow_0 @ sk_A @ X0)
% 3.33/3.56          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 3.33/3.56             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56          | ~ (v5_orders_2 @ sk_A))),
% 3.33/3.56      inference('sup-', [status(thm)], ['116', '117'])).
% 3.33/3.56  thf('119', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('120', plain, ((v5_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('121', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56          | ~ (r1_yellow_0 @ sk_A @ X0)
% 3.33/3.56          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 3.33/3.56             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.56      inference('demod', [status(thm)], ['118', '119', '120'])).
% 3.33/3.56  thf('122', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (~ (v1_xboole_0 @ X0)
% 3.33/3.56          | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 3.33/3.56             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56          | ~ (r1_yellow_0 @ sk_A @ X0)
% 3.33/3.56          | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['115', '121'])).
% 3.33/3.56  thf('123', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (~ (r1_yellow_0 @ sk_A @ X0)
% 3.33/3.56          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 3.33/3.56             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56          | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56          | ~ (v1_xboole_0 @ X0))),
% 3.33/3.56      inference('simplify', [status(thm)], ['122'])).
% 3.33/3.56  thf('124', plain,
% 3.33/3.56      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.33/3.56         | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56         | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.33/3.56            (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['106', '123'])).
% 3.33/3.56  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.33/3.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.33/3.56  thf('126', plain,
% 3.33/3.56      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_yellow_0 @ sk_A) @ sk_A))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('clc', [status(thm)], ['102', '103'])).
% 3.33/3.56  thf('127', plain,
% 3.33/3.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.33/3.56         (((X27) = (k1_yellow_0 @ X25 @ X26))
% 3.33/3.56          | ~ (zip_tseitin_2 @ X26 @ X27 @ X25))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.33/3.56  thf('128', plain,
% 3.33/3.56      ((((k3_yellow_0 @ sk_A) = (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['126', '127'])).
% 3.33/3.56  thf('129', plain,
% 3.33/3.56      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56         | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 3.33/3.56            (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('demod', [status(thm)], ['124', '125', '128'])).
% 3.33/3.56  thf('130', plain,
% 3.33/3.56      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['48', '51'])).
% 3.33/3.56  thf('131', plain,
% 3.33/3.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf(d20_waybel_0, axiom,
% 3.33/3.56    (![A:$i]:
% 3.33/3.56     ( ( l1_orders_2 @ A ) =>
% 3.33/3.56       ( ![B:$i]:
% 3.33/3.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.33/3.56           ( ( v13_waybel_0 @ B @ A ) <=>
% 3.33/3.56             ( ![C:$i]:
% 3.33/3.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56                 ( ![D:$i]:
% 3.33/3.56                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.33/3.56                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 3.33/3.56                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 3.33/3.56  thf('132', plain,
% 3.33/3.56      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.33/3.56          | ~ (v13_waybel_0 @ X34 @ X35)
% 3.33/3.56          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 3.33/3.56          | (r2_hidden @ X36 @ X34)
% 3.33/3.56          | ~ (r1_orders_2 @ X35 @ X37 @ X36)
% 3.33/3.56          | ~ (r2_hidden @ X37 @ X34)
% 3.33/3.56          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 3.33/3.56          | ~ (l1_orders_2 @ X35))),
% 3.33/3.56      inference('cnf', [status(esa)], [d20_waybel_0])).
% 3.33/3.56  thf('133', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ sk_A)
% 3.33/3.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.33/3.56          | ~ (r2_hidden @ X0 @ sk_B_1)
% 3.33/3.56          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 3.33/3.56          | (r2_hidden @ X1 @ sk_B_1)
% 3.33/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.33/3.56          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 3.33/3.56      inference('sup-', [status(thm)], ['131', '132'])).
% 3.33/3.56  thf('134', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('135', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('136', plain,
% 3.33/3.56      (![X0 : $i, X1 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.33/3.56          | ~ (r2_hidden @ X0 @ sk_B_1)
% 3.33/3.56          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 3.33/3.56          | (r2_hidden @ X1 @ sk_B_1)
% 3.33/3.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('demod', [status(thm)], ['133', '134', '135'])).
% 3.33/3.56  thf('137', plain,
% 3.33/3.56      ((![X0 : $i]:
% 3.33/3.56          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.33/3.56           | (r2_hidden @ X0 @ sk_B_1)
% 3.33/3.56           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 3.33/3.56           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['130', '136'])).
% 3.33/3.56  thf('138', plain,
% 3.33/3.56      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('split', [status(esa)], ['0'])).
% 3.33/3.56  thf('139', plain,
% 3.33/3.56      ((![X0 : $i]:
% 3.33/3.56          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.33/3.56           | (r2_hidden @ X0 @ sk_B_1)
% 3.33/3.56           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('demod', [status(thm)], ['137', '138'])).
% 3.33/3.56  thf('140', plain,
% 3.33/3.56      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56         | (r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 3.33/3.56         | ~ (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.33/3.56              (u1_struct_0 @ sk_A))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['129', '139'])).
% 3.33/3.56  thf('141', plain,
% 3.33/3.56      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.33/3.56           (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['107', '108'])).
% 3.33/3.56  thf('142', plain,
% 3.33/3.56      ((((r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 3.33/3.56         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('clc', [status(thm)], ['140', '141'])).
% 3.33/3.56  thf('143', plain,
% 3.33/3.56      (![X3 : $i, X4 : $i]:
% 3.33/3.56         (~ (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 3.33/3.56          | ((X4) = (X3))
% 3.33/3.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 3.33/3.56      inference('cnf', [status(esa)], [t49_subset_1])).
% 3.33/3.56  thf('144', plain,
% 3.33/3.56      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 3.33/3.56         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['142', '143'])).
% 3.33/3.56  thf('145', plain,
% 3.33/3.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('146', plain,
% 3.33/3.56      (((((u1_struct_0 @ sk_A) = (sk_B_1)) | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('demod', [status(thm)], ['144', '145'])).
% 3.33/3.56  thf('147', plain,
% 3.33/3.56      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['146'])).
% 3.33/3.56  thf('148', plain,
% 3.33/3.56      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 3.33/3.56        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('149', plain,
% 3.33/3.56      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.56      inference('split', [status(esa)], ['148'])).
% 3.33/3.56  thf('150', plain,
% 3.33/3.56      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 3.33/3.56         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 3.33/3.56             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup+', [status(thm)], ['147', '149'])).
% 3.33/3.56  thf('151', plain,
% 3.33/3.56      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['146'])).
% 3.33/3.56  thf('152', plain,
% 3.33/3.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('153', plain,
% 3.33/3.56      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup+', [status(thm)], ['151', '152'])).
% 3.33/3.56  thf(d7_subset_1, axiom,
% 3.33/3.56    (![A:$i,B:$i]:
% 3.33/3.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.33/3.56       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 3.33/3.56  thf('154', plain,
% 3.33/3.56      (![X38 : $i, X39 : $i]:
% 3.33/3.56         (~ (v1_subset_1 @ X39 @ X38)
% 3.33/3.56          | ((X39) != (X38))
% 3.33/3.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 3.33/3.56      inference('cnf', [status(esa)], [d7_subset_1])).
% 3.33/3.56  thf('155', plain,
% 3.33/3.56      (![X38 : $i]:
% 3.33/3.56         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X38))
% 3.33/3.56          | ~ (v1_subset_1 @ X38 @ X38))),
% 3.33/3.56      inference('simplify', [status(thm)], ['154'])).
% 3.33/3.56  thf('156', plain,
% 3.33/3.56      ((~ (v1_subset_1 @ sk_B_1 @ sk_B_1))
% 3.33/3.56         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['153', '155'])).
% 3.33/3.56  thf('157', plain,
% 3.33/3.56      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 3.33/3.56       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['150', '156'])).
% 3.33/3.56  thf('158', plain,
% 3.33/3.56      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 3.33/3.56       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('split', [status(esa)], ['148'])).
% 3.33/3.56  thf('159', plain,
% 3.33/3.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('160', plain,
% 3.33/3.56      (![X38 : $i, X39 : $i]:
% 3.33/3.56         (((X39) = (X38))
% 3.33/3.56          | (v1_subset_1 @ X39 @ X38)
% 3.33/3.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 3.33/3.56      inference('cnf', [status(esa)], [d7_subset_1])).
% 3.33/3.56  thf('161', plain,
% 3.33/3.56      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 3.33/3.56        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['159', '160'])).
% 3.33/3.56  thf('162', plain,
% 3.33/3.56      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.33/3.56         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.56      inference('split', [status(esa)], ['0'])).
% 3.33/3.56  thf('163', plain,
% 3.33/3.56      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 3.33/3.56         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.56      inference('sup-', [status(thm)], ['161', '162'])).
% 3.33/3.56  thf('164', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 3.33/3.56      inference('simplify', [status(thm)], ['6'])).
% 3.33/3.56  thf(t2_subset, axiom,
% 3.33/3.56    (![A:$i,B:$i]:
% 3.33/3.56     ( ( m1_subset_1 @ A @ B ) =>
% 3.33/3.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.33/3.56  thf('165', plain,
% 3.33/3.56      (![X5 : $i, X6 : $i]:
% 3.33/3.56         ((r2_hidden @ X5 @ X6)
% 3.33/3.56          | (v1_xboole_0 @ X6)
% 3.33/3.56          | ~ (m1_subset_1 @ X5 @ X6))),
% 3.33/3.56      inference('cnf', [status(esa)], [t2_subset])).
% 3.33/3.56  thf('166', plain,
% 3.33/3.56      (![X0 : $i]:
% 3.33/3.56         (~ (l1_orders_2 @ X0)
% 3.33/3.56          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.33/3.56          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['164', '165'])).
% 3.33/3.56  thf('167', plain,
% 3.33/3.56      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 3.33/3.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.33/3.56         | ~ (l1_orders_2 @ sk_A)))
% 3.33/3.56         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.56      inference('sup+', [status(thm)], ['163', '166'])).
% 3.33/3.56  thf('168', plain,
% 3.33/3.56      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 3.33/3.56         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.56      inference('sup-', [status(thm)], ['161', '162'])).
% 3.33/3.56  thf('169', plain, ((l1_orders_2 @ sk_A)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('170', plain,
% 3.33/3.56      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 3.33/3.56         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.56      inference('demod', [status(thm)], ['167', '168', '169'])).
% 3.33/3.56  thf('171', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.33/3.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.56  thf('172', plain,
% 3.33/3.56      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 3.33/3.56         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.33/3.56      inference('clc', [status(thm)], ['170', '171'])).
% 3.33/3.56  thf('173', plain,
% 3.33/3.56      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 3.33/3.56         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.33/3.56      inference('split', [status(esa)], ['148'])).
% 3.33/3.56  thf('174', plain,
% 3.33/3.56      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 3.33/3.56       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.33/3.56      inference('sup-', [status(thm)], ['172', '173'])).
% 3.33/3.56  thf('175', plain, ($false),
% 3.33/3.56      inference('sat_resolution*', [status(thm)], ['1', '157', '158', '174'])).
% 3.33/3.56  
% 3.33/3.56  % SZS output end Refutation
% 3.33/3.56  
% 3.33/3.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
