%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1187+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DwHoJGgOl7

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:13 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  217 (1449 expanded)
%              Number of leaves         :   44 ( 412 expanded)
%              Depth                    :   39
%              Number of atoms          : 2060 (21926 expanded)
%              Number of equality atoms :   41 ( 262 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r6_orders_1_type,type,(
    r6_orders_1: $i > $i > $o )).

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

thf(t159_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r6_orders_1 @ ( u1_orders_2 @ A ) @ B )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( r2_orders_2 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( r6_orders_1 @ ( u1_orders_2 @ A ) @ B )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( r2_orders_2 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t159_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc5_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( v8_relat_2 @ ( u1_orders_2 @ A ) ) ) )).

thf('8',plain,(
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

thf('9',plain,(
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

thf('10',plain,(
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

thf('11',plain,(
    ! [X16: $i] :
      ( ( v1_partfun1 @ ( u1_orders_2 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_orders_2])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v1_partfun1 @ X22 @ X21 )
      | ~ ( v8_relat_2 @ X22 )
      | ~ ( v4_relat_2 @ X22 )
      | ~ ( v1_relat_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t100_orders_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_partfun1 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
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
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v8_relat_2 @ ( u1_orders_2 @ X0 ) )
      | ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
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
    inference('sup-',[status(thm)],['8','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d11_orders_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r6_orders_1 @ A @ B )
        <=> ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
            & ! [C: $i] :
                ~ ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                  & ( C != B )
                  & ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_C @ X7 @ X8 ) ) @ X8 )
      | ( r6_orders_1 @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r6_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ( r6_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( r6_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) @ ( u1_orders_2 @ sk_A ) )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v2_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_orders_2 @ A )
       => ( v2_orders_2 @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_orders_2])).

thf('34',plain,
    ( ( v2_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) @ ( u1_orders_2 @ sk_A ) )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29','30','31','36'])).

thf('38',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
   <= ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['38'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X27 )
      | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
   <= ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('52',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_orders_2 @ X5 @ X4 @ X6 )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( u1_orders_2 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('67',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r6_orders_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ X8 ) )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ( X1 = X2 )
      | ~ ( r6_orders_1 @ ( u1_orders_2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( sk_C_1 = sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v2_orders_2 @ sk_A )
      | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('75',plain,
    ( ( ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      | ( sk_C_1 = sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74'])).

thf('76',plain,
    ( ( ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_C_1 = sk_B ) )
   <= ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','75'])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
   <= ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','76'])).

thf('78',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( sk_C_1 = sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( sk_C_1 = sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('81',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('82',plain,
    ( ( ( sk_C_1 = sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('84',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( sk_C_1 = sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_C_1 = sk_B )
   <= ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('90',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 )
   <= ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('92',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_orders_2 @ X5 @ X4 @ X6 )
      | ( X4 != X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('93',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( r2_orders_2 @ X5 @ X6 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C_1 @ sk_C_1 )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['40','42','97'])).

thf('99',plain,(
    ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['39','98'])).

thf('100',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) @ ( u1_orders_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','99'])).

thf('101',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( u1_orders_2 @ X12 ) )
      | ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('110',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ ( k3_relat_1 @ X8 ) )
      | ( r6_orders_1 @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r6_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ( r6_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( r6_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v2_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('120',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( k3_relat_1 @ ( u1_orders_2 @ sk_A ) ) )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119'])).

thf('121',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['106','120'])).

thf('122',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('123',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126'])).

thf('128',plain,(
    ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['39','98'])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('130',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('131',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ( X4 = X6 )
      | ( r2_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
    | ( sk_B
      = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
    | ( sk_B
      = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','139'])).

thf('141',plain,
    ( ( sk_B
      = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('143',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_orders_2 @ sk_A @ sk_B @ X27 ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_orders_2 @ sk_A @ sk_B @ X27 ) ) ),
    inference(split,[status(esa)],['47'])).

thf('144',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_orders_2 @ sk_A @ sk_B @ X27 ) )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['47'])).

thf('145',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X27 ) ) ),
    inference('sat_resolution*',[status(thm)],['40','42','97','144'])).

thf('146',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X27 ) ) ),
    inference(simpl_trail,[status(thm)],['143','145'])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['141','147'])).

thf('149',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( u1_orders_2 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v2_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('151',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_relat_1 @ X8 ) )
      | ( ( sk_C @ X7 @ X8 )
       != X7 )
      | ( r6_orders_1 @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r6_orders_1 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) )
     != sk_B )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v2_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_orders_2 @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('159',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ sk_B @ ( u1_orders_2 @ sk_A ) )
     != sk_B )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158'])).

thf('160',plain,
    ( ( sk_B != sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','159'])).

thf('161',plain,
    ( ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ~ ( r6_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['39','98'])).

thf('163',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','163'])).

thf('165',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf('170',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    $false ),
    inference(demod,[status(thm)],['0','170'])).


%------------------------------------------------------------------------------
