%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SaqtlJhWSi

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:11 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 286 expanded)
%              Number of leaves         :   50 ( 114 expanded)
%              Depth                    :   30
%              Number of atoms          : 1250 (2903 expanded)
%              Number of equality atoms :   22 (  87 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t14_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
         => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
            = ( k3_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_yellow_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k4_yellow_0 @ A )
        = ( k2_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X27: $i] :
      ( ( ( k4_yellow_0 @ X27 )
        = ( k2_yellow_0 @ X27 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d12_yellow_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('3',plain,(
    r2_hidden @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('5',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X52: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X17 @ X16 ) @ X17 )
      | ( r1_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X46: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_tarski @ sk_A ) @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k3_tarski @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ ( k3_tarski @ sk_A ) @ X0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X52: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t31_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) )
               => ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_1 @ X33 @ X34 @ X35 @ X36 )
      | ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X52: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k2_yellow_0 @ A @ C ) )
        & ( r2_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r1_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ D @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k2_yellow_0 @ A @ C ) )
                  & ( r2_yellow_0 @ A @ C ) )
               => ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X40: $i,X41: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r1_lattice3 @ X41 @ X44 @ X40 )
      | ~ ( zip_tseitin_1 @ ( sk_D_3 @ X44 @ X40 @ X41 ) @ X44 @ X40 @ X41 )
      | ( zip_tseitin_2 @ X44 @ X40 @ X41 )
      | ~ ( l1_orders_2 @ X41 )
      | ~ ( v5_orders_2 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_3 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X50: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('22',plain,(
    ! [X46: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_3 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('27',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('34',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('36',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( u1_struct_0 @ ( k2_yellow_1 @ X55 ) ) )
      | ~ ( r1_tarski @ X54 @ X56 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X55 ) @ X54 @ X56 )
      | ~ ( m1_subset_1 @ X56 @ ( u1_struct_0 @ ( k2_yellow_1 @ X55 ) ) )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('37',plain,(
    ! [X52: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('38',plain,(
    ! [X52: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('39',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X54 @ X55 )
      | ~ ( r1_tarski @ X54 @ X56 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X55 ) @ X54 @ X56 )
      | ~ ( m1_subset_1 @ X56 @ X55 )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('43',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X52: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ X9 @ X11 )
      | ~ ( r3_orders_2 @ X10 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X52: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('51',plain,(
    ! [X48: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('52',plain,(
    ! [X46: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('56',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ~ ( r1_orders_2 @ X32 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_1 @ X33 @ X34 @ X35 @ X36 )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D_3 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_3 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('64',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('66',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('67',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X39
        = ( k2_yellow_0 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_2 @ X38 @ X39 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( k3_tarski @ sk_A )
      = ( k2_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k3_tarski @ sk_A )
      = ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','70'])).

thf('72',plain,(
    ! [X46: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('73',plain,
    ( ( ( k3_tarski @ sk_A )
      = ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != ( k3_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('76',plain,(
    ! [X51: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X51 ) )
      | ( v1_xboole_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('77',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SaqtlJhWSi
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:08:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 351 iterations in 0.246s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.70  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.46/0.70  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.70  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.46/0.70  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.46/0.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.70  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.46/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.46/0.70  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.46/0.70  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.46/0.70  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.46/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.70  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.70  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.46/0.70  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.46/0.70  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.46/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.46/0.70  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.70  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.46/0.70  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.46/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.70  thf(t14_yellow_1, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.70       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.46/0.70         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.70          ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.46/0.70            ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t14_yellow_1])).
% 0.46/0.70  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(d12_yellow_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_orders_2 @ A ) =>
% 0.46/0.70       ( ( k4_yellow_0 @ A ) = ( k2_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X27 : $i]:
% 0.46/0.70         (((k4_yellow_0 @ X27) = (k2_yellow_0 @ X27 @ k1_xboole_0))
% 0.46/0.70          | ~ (l1_orders_2 @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [d12_yellow_0])).
% 0.46/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.70  thf('2', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.70  thf('3', plain, ((r2_hidden @ (k3_tarski @ sk_A) @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t1_subset, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_subset])).
% 0.46/0.70  thf('5', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf(t1_yellow_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.46/0.70       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.70  thf('6', plain, (![X52 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X52)) = (X52))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.70  thf(d8_lattice3, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_orders_2 @ A ) =>
% 0.46/0.70       ( ![B:$i,C:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.46/0.70             ( ![D:$i]:
% 0.46/0.70               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.46/0.70          | (r2_hidden @ (sk_D @ X15 @ X17 @ X16) @ X17)
% 0.46/0.70          | (r1_lattice3 @ X16 @ X17 @ X15)
% 0.46/0.70          | ~ (l1_orders_2 @ X16))),
% 0.46/0.70      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.70          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.46/0.70          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.46/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.70  thf(dt_k2_yellow_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.70       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.46/0.70  thf('9', plain, (![X46 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X46))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.70          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.46/0.70          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.46/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r2_hidden @ 
% 0.46/0.70           (sk_D @ (k3_tarski @ sk_A) @ X0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.46/0.70          | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ (k3_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['5', '10'])).
% 0.46/0.70  thf(t7_ordinal1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ (k3_tarski @ sk_A))
% 0.46/0.70          | ~ (r1_tarski @ X0 @ 
% 0.46/0.70               (sk_D @ (k3_tarski @ sk_A) @ X0 @ (k2_yellow_1 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ (k3_tarski @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['2', '13'])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X52 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X52)) = (X52))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.70  thf(t31_yellow_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( ( ( r2_yellow_0 @ A @ C ) & 
% 0.46/0.70                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) =>
% 0.46/0.70                 ( ( ![D:$i]:
% 0.46/0.70                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.46/0.70                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 0.46/0.70                   ( r1_lattice3 @ A @ C @ B ) ) ) & 
% 0.46/0.70               ( ( ( ![D:$i]:
% 0.46/0.70                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.46/0.70                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 0.46/0.70                   ( r1_lattice3 @ A @ C @ B ) ) =>
% 0.46/0.70                 ( ( r2_yellow_0 @ A @ C ) & 
% 0.46/0.70                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_1, axiom,
% 0.46/0.70    (![D:$i,C:$i,B:$i,A:$i]:
% 0.46/0.70     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.46/0.70       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.70         ((zip_tseitin_1 @ X33 @ X34 @ X35 @ X36)
% 0.46/0.70          | (m1_subset_1 @ X33 @ (u1_struct_0 @ X36)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.70         ((m1_subset_1 @ X1 @ X0)
% 0.46/0.70          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (![X52 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X52)) = (X52))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.70  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.46/0.70  thf(zf_stmt_3, axiom,
% 0.46/0.70    (![C:$i,B:$i,A:$i]:
% 0.46/0.70     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.46/0.70       ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & ( r2_yellow_0 @ A @ C ) ) ))).
% 0.46/0.70  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.46/0.70  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.70  thf(zf_stmt_6, axiom,
% 0.46/0.70    (![D:$i,C:$i,B:$i,A:$i]:
% 0.46/0.70     ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ D @ B ) ) =>
% 0.46/0.70       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.46/0.70  thf(zf_stmt_7, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( ( ( r1_lattice3 @ A @ C @ B ) & 
% 0.46/0.70                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.46/0.70                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.46/0.70               ( ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & 
% 0.46/0.70                   ( r2_yellow_0 @ A @ C ) ) =>
% 0.46/0.70                 ( ( r1_lattice3 @ A @ C @ B ) & 
% 0.46/0.70                   ( ![D:$i]:
% 0.46/0.70                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.46/0.70                         ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X40 : $i, X41 : $i, X44 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 0.46/0.70          | ~ (r1_lattice3 @ X41 @ X44 @ X40)
% 0.46/0.70          | ~ (zip_tseitin_1 @ (sk_D_3 @ X44 @ X40 @ X41) @ X44 @ X40 @ X41)
% 0.46/0.70          | (zip_tseitin_2 @ X44 @ X40 @ X41)
% 0.46/0.70          | ~ (l1_orders_2 @ X41)
% 0.46/0.70          | ~ (v5_orders_2 @ X41))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.70          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (zip_tseitin_1 @ (sk_D_3 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.46/0.70               X1 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf(fc5_yellow_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.70       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.70       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.70       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.46/0.70  thf('21', plain, (![X50 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X50))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.70  thf('22', plain, (![X46 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X46))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.70          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (zip_tseitin_1 @ (sk_D_3 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.46/0.70               X1 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((m1_subset_1 @ (sk_D_3 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.46/0.70          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.46/0.70          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['17', '23'])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      ((~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (m1_subset_1 @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '24'])).
% 0.46/0.70  thf('26', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (m1_subset_1 @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (m1_subset_1 @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.70  thf(t2_subset, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.70       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         ((r2_hidden @ X5 @ X6)
% 0.46/0.70          | (v1_xboole_0 @ X6)
% 0.46/0.70          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (v1_xboole_0 @ sk_A)
% 0.46/0.70        | (r2_hidden @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf('31', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (((r2_hidden @ 
% 0.46/0.70         (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70         sk_A)
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('clc', [status(thm)], ['30', '31'])).
% 0.46/0.70  thf(l49_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X1 : $i, X2 : $i]:
% 0.46/0.70         ((r1_tarski @ X1 @ (k3_tarski @ X2)) | ~ (r2_hidden @ X1 @ X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (r1_tarski @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (m1_subset_1 @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.70  thf(t3_yellow_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.70               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.46/0.70                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X54 @ (u1_struct_0 @ (k2_yellow_1 @ X55)))
% 0.46/0.70          | ~ (r1_tarski @ X54 @ X56)
% 0.46/0.70          | (r3_orders_2 @ (k2_yellow_1 @ X55) @ X54 @ X56)
% 0.46/0.70          | ~ (m1_subset_1 @ X56 @ (u1_struct_0 @ (k2_yellow_1 @ X55)))
% 0.46/0.70          | (v1_xboole_0 @ X55))),
% 0.46/0.70      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X52 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X52)) = (X52))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X52 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X52)) = (X52))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X54 @ X55)
% 0.46/0.70          | ~ (r1_tarski @ X54 @ X56)
% 0.46/0.70          | (r3_orders_2 @ (k2_yellow_1 @ X55) @ X54 @ X56)
% 0.46/0.70          | ~ (m1_subset_1 @ X56 @ X55)
% 0.46/0.70          | (v1_xboole_0 @ X55))),
% 0.46/0.70      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A))
% 0.46/0.70          | (v1_xboole_0 @ sk_A)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.46/0.70          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70             (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70             X0)
% 0.46/0.70          | ~ (r1_tarski @ 
% 0.46/0.70               (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70                (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70               X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['35', '39'])).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A))
% 0.46/0.70        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.46/0.70        | (v1_xboole_0 @ sk_A)
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['34', '40'])).
% 0.46/0.70  thf('42', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A))
% 0.46/0.70        | (v1_xboole_0 @ sk_A)
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      (((v1_xboole_0 @ sk_A)
% 0.46/0.70        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A))
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.70  thf('45', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A)))),
% 0.46/0.70      inference('clc', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      (![X52 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X52)) = (X52))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.70  thf(redefinition_r3_orders_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.70         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.46/0.70          | ~ (l1_orders_2 @ X10)
% 0.46/0.70          | ~ (v3_orders_2 @ X10)
% 0.46/0.70          | (v2_struct_0 @ X10)
% 0.46/0.70          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.46/0.70          | (r1_orders_2 @ X10 @ X9 @ X11)
% 0.46/0.70          | ~ (r3_orders_2 @ X10 @ X9 @ X11))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.70          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.70          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.70          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      (![X52 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X52)) = (X52))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.70  thf('51', plain, (![X48 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X48))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.70  thf('52', plain, (![X46 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X46))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.70          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.70          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.70          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.70          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.46/0.70        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A))
% 0.46/0.70        | ~ (m1_subset_1 @ 
% 0.46/0.70             (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70             sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['46', '53'])).
% 0.46/0.70  thf('55', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A))
% 0.46/0.70        | ~ (m1_subset_1 @ 
% 0.46/0.70             (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70             sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A))
% 0.46/0.70        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['27', '56'])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70           (k3_tarski @ sk_A))
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.70         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.46/0.70          | ~ (r1_orders_2 @ X32 @ X29 @ X31))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A))
% 0.46/0.70          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70          | (zip_tseitin_0 @ 
% 0.46/0.70             (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70             X0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.70         ((zip_tseitin_1 @ X33 @ X34 @ X35 @ X36)
% 0.46/0.70          | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70          | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70             (k2_yellow_1 @ sk_A))
% 0.46/0.70          | (zip_tseitin_1 @ 
% 0.46/0.70             (sk_D_3 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.46/0.70             X0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.70          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (zip_tseitin_1 @ (sk_D_3 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.46/0.70               X1 @ (k2_yellow_1 @ X0))
% 0.46/0.70          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | ~ (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.46/0.70             (k3_tarski @ sk_A))
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A))
% 0.46/0.70        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ (k3_tarski @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['2', '13'])).
% 0.46/0.70  thf('66', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70         (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.46/0.70  thf('68', plain,
% 0.46/0.70      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.46/0.70           (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.70         (((X39) = (k2_yellow_0 @ X37 @ X38))
% 0.46/0.70          | ~ (zip_tseitin_2 @ X38 @ X39 @ X37))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | ((k3_tarski @ sk_A)
% 0.46/0.70            = (k2_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      ((((k3_tarski @ sk_A) = (k4_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.70        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.46/0.70        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['1', '70'])).
% 0.46/0.70  thf('72', plain, (![X46 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X46))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      ((((k3_tarski @ sk_A) = (k4_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.70        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.70  thf('74', plain,
% 0.46/0.70      (((k4_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k3_tarski @ sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('75', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.46/0.70  thf(fc6_yellow_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.70       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.46/0.70         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.46/0.70  thf('76', plain,
% 0.46/0.70      (![X51 : $i]:
% 0.46/0.70         (~ (v2_struct_0 @ (k2_yellow_1 @ X51)) | (v1_xboole_0 @ X51))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.46/0.70  thf('77', plain, ((v1_xboole_0 @ sk_A)),
% 0.46/0.70      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.70  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
