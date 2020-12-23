%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1188+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3qVs1UmwQp

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:13 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 678 expanded)
%              Number of leaves         :   44 ( 211 expanded)
%              Depth                    :   43
%              Number of atoms          : 2473 (10825 expanded)
%              Number of equality atoms :   93 ( 355 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r8_orders_1_type,type,(
    r8_orders_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_orders_2_type,type,(
    v2_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t160_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r8_orders_1 @ ( u1_orders_2 @ A ) @ B )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( B != C )
                 => ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( r8_orders_1 @ ( u1_orders_2 @ A ) @ B )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( B != C )
                   => ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t160_orders_2])).

thf('0',plain,
    ( ( sk_B != sk_C_1 )
    | ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != sk_C_1 )
    | ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X27 @ sk_B )
      | ( sk_B = X27 )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
   <= ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc5_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( v8_relat_2 @ ( u1_orders_2 @ A ) ) ) )).

thf('14',plain,(
    ! [X20: $i] :
      ( ( v8_relat_2 @ ( u1_orders_2 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v2_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_orders_2])).

thf(fc4_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( v4_relat_2 @ ( u1_orders_2 @ A ) ) ) )).

thf('15',plain,(
    ! [X19: $i] :
      ( ( v4_relat_2 @ ( u1_orders_2 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v2_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_orders_2])).

thf(fc3_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( v1_relat_2 @ ( u1_orders_2 @ A ) ) ) )).

thf('16',plain,(
    ! [X18: $i] :
      ( ( v1_relat_2 @ ( u1_orders_2 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_orders_2])).

thf(fc2_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( v1_partfun1 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( v1_partfun1 @ ( u1_orders_2 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_orders_2])).

thf('18',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(t100_orders_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_2 @ B )
        & ( v4_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k3_relat_1 @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v1_partfun1 @ X22 @ X21 )
      | ~ ( v8_relat_2 @ X22 )
      | ~ ( v4_relat_2 @ X22 )
      | ~ ( v1_relat_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t100_orders_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_partfun1 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(d13_orders_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r8_orders_1 @ A @ B )
        <=> ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
            & ! [C: $i] :
                ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
               => ( ( C = B )
                  | ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r8_orders_1 @ X8 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X8 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( X1 = X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r8_orders_1 @ ( u1_orders_2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r8_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ( X2 = X1 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( X2 = X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r8_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        | ( X0 = sk_B )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v2_orders_2 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_orders_2 @ A )
       => ( v2_orders_2 @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_orders_2])).

thf('40',plain,
    ( ( v2_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
        | ( X0 = sk_B )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','42'])).

thf('44',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) )
   <= ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','43'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( u1_orders_2 @ X12 ) )
      | ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('46',plain,
    ( ( ( sk_C_1 = sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('50',plain,
    ( ( ( sk_C_1 = sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ( X4 = X6 )
      | ( r2_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ sk_C_1 @ X0 )
        | ( sk_C_1 = X0 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ sk_C_1 @ X0 )
        | ( sk_C_1 = X0 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ( sk_C_1 = sk_B )
      | ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ( sk_C_1 = sk_B ) )
   <= ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ( sk_C_1 = sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('61',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C_1 = sk_B ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('63',plain,
    ( ( ( sk_C_1 = sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('65',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( sk_C_1 = sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_C_1 = sk_B )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B != sk_C_1 )
   <= ( sk_B != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ( sk_B != sk_C_1 )
      & ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B = sk_C_1 )
    | ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ ( k3_relat_1 @ X8 ) )
      | ( r8_orders_1 @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( r8_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v2_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93'])).

thf('95',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['80','94'])).

thf('96',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('97',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('102',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('105',plain,
    ( ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('107',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_orders_2 @ X5 @ X4 @ X6 )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ sk_B )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('116',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( u1_orders_2 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X7 @ X8 ) @ X7 ) @ X8 )
      | ( r8_orders_1 @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_1])).

thf('125',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','126'])).

thf('128',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('129',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132'])).

thf('134',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','133'])).

thf('135',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','135'])).

thf('137',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('141',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_relat_1 @ X8 ) )
      | ( ( sk_C @ X7 @ X8 )
       != X7 )
      | ( r8_orders_1 @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) )
     != sk_B )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v2_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('149',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) )
     != sk_B )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147','148'])).

thf('150',plain,
    ( ( ( sk_B != sk_B )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','149'])).

thf('151',plain,
    ( ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','151'])).

thf('153',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_B = X27 )
        | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
   <= ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('156',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
          | ( sk_B = X27 )
          | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
          | ( sk_B = X27 )
          | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
          | ( sk_B = X27 )
          | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
          | ( sk_B = X27 )
          | ( r2_orders_2 @ sk_A @ X27 @ sk_B ) )
    | ( r8_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','72','73','162'])).


%------------------------------------------------------------------------------
