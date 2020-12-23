%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1146+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rOTTYVZOnx

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:09 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  244 (2645 expanded)
%              Number of leaves         :   39 ( 731 expanded)
%              Depth                    :   28
%              Number of atoms          : 2586 (67480 expanded)
%              Number of equality atoms :   17 ( 235 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t38_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ~ ( ? [D: $i] :
                        ( ( r2_hidden @ C @ D )
                        & ( r2_hidden @ B @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( v6_orders_2 @ D @ A ) )
                    & ~ ( r1_orders_2 @ A @ B @ C )
                    & ~ ( r1_orders_2 @ A @ C @ B ) )
                & ~ ( ( ( r1_orders_2 @ A @ B @ C )
                      | ( r1_orders_2 @ A @ C @ B ) )
                    & ! [D: $i] :
                        ( ( ( v6_orders_2 @ D @ A )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( r2_hidden @ B @ D )
                            & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ~ ( ? [D: $i] :
                          ( ( r2_hidden @ C @ D )
                          & ( r2_hidden @ B @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                          & ( v6_orders_2 @ D @ A ) )
                      & ~ ( r1_orders_2 @ A @ B @ C )
                      & ~ ( r1_orders_2 @ A @ C @ B ) )
                  & ~ ( ( ( r1_orders_2 @ A @ B @ C )
                        | ( r1_orders_2 @ A @ C @ B ) )
                      & ! [D: $i] :
                          ( ( ( v6_orders_2 @ D @ A )
                            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                         => ~ ( ( r2_hidden @ B @ D )
                              & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_orders_2])).

thf('0',plain,(
    ! [X41: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ X41 )
      | ~ ( r2_hidden @ sk_B @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ X31 )
      | ( ( k7_domain_1 @ X31 @ X30 @ X32 )
        = ( k2_tarski @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_tarski @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( v6_orders_2 @ sk_D_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 )
      | ~ ( v3_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( r3_orders_2 @ X34 @ X33 @ X35 )
      | ~ ( r1_orders_2 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X29: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ~ ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X3 ) ) )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_orders_2 @ X22 @ X21 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( u1_orders_2 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('33',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('38',plain,(
    ! [X27: $i] :
      ( ( l1_struct_0 @ X27 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v2_struct_0 @ sk_A )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('41',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['18','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A )
                  & ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
              <=> ( ( r3_orders_2 @ A @ B @ C )
                  | ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r3_orders_2 @ X37 @ X36 @ X38 )
      | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ X37 ) @ X36 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( l1_orders_2 @ X37 )
      | ~ ( v3_orders_2 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t36_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,
    ( ~ ( v2_struct_0 @ sk_A )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('52',plain,
    ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['7','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( m1_subset_1 @ ( k7_domain_1 @ X25 @ X24 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_domain_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X41: $i] :
      ( ( v6_orders_2 @ sk_D_2 @ sk_A )
      | ~ ( r2_hidden @ sk_C_1 @ X41 )
      | ~ ( r2_hidden @ sk_B @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
      | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) )
   <= ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('66',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('67',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('70',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','68','69'])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('78',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','78'])).

thf('80',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_D_2 )
   <= ( r2_hidden @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,
    ( ( v6_orders_2 @ sk_D_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('88',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['81'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ X31 )
      | ( ( k7_domain_1 @ X31 @ X30 @ X32 )
        = ( k2_tarski @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_tarski @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B )
      = ( k2_tarski @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B )
      = ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('97',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 )
      | ~ ( v3_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( r3_orders_2 @ X34 @ X33 @ X35 )
      | ~ ( r1_orders_2 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('107',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_orders_2 @ X22 @ X21 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( u1_orders_2 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','114'])).

thf('116',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['106','117'])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('121',plain,
    ( ~ ( v2_struct_0 @ sk_A )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['105','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r3_orders_2 @ X37 @ X36 @ X38 )
      | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ X37 ) @ X36 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( l1_orders_2 @ X37 )
      | ~ ( v3_orders_2 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t36_orders_2])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','129'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['122','130'])).

thf('132',plain,
    ( ~ ( v2_struct_0 @ sk_A )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('133',plain,
    ( ( v6_orders_2 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) @ sk_A )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['95','133'])).

thf('135',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v6_orders_2 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','68','69'])).

thf('136',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('139',plain,
    ( ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
   <= ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('143',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
   <= ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['83'])).

thf('145',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_D_2 )
   <= ( r2_hidden @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['81'])).

thf('146',plain,
    ( ( v6_orders_2 @ sk_D_2 @ sk_A )
   <= ( v6_orders_2 @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('147',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['85'])).

thf('148',plain,
    ( ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) )
   <= ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['62'])).

thf('149',plain,
    ( ( ~ ( v6_orders_2 @ sk_D_2 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ sk_D_2 )
      | ~ ( r2_hidden @ sk_C_1 @ sk_D_2 ) )
   <= ( ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ~ ( r2_hidden @ sk_C_1 @ sk_D_2 )
      | ~ ( r2_hidden @ sk_B @ sk_D_2 ) )
   <= ( ( v6_orders_2 @ sk_D_2 @ sk_A )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
   <= ( ( v6_orders_2 @ sk_D_2 @ sk_A )
      & ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( r2_hidden @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,
    ( ~ ! [X41: $i] :
          ( ~ ( r2_hidden @ sk_C_1 @ X41 )
          | ~ ( r2_hidden @ sk_B @ X41 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v6_orders_2 @ X41 @ sk_A ) )
    | ~ ( v6_orders_2 @ sk_D_2 @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ sk_D_2 )
    | ~ ( r2_hidden @ sk_B @ sk_D_2 )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['144','151'])).

thf('153',plain,(
    ! [X41: $i] :
      ( ( r2_hidden @ sk_C_1 @ sk_D_2 )
      | ~ ( r2_hidden @ sk_C_1 @ X41 )
      | ~ ( r2_hidden @ sk_B @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_D_2 )
    | ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['153'])).

thf('155',plain,(
    r2_hidden @ sk_C_1 @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['84','86','87','88','2','78','143','152','154'])).

thf('156',plain,(
    r2_hidden @ sk_C_1 @ sk_D_2 ),
    inference(simpl_trail,[status(thm)],['82','155'])).

thf('157',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
   <= ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['83'])).

thf('158',plain,(
    ! [X41: $i] :
      ( ( r2_hidden @ sk_B @ sk_D_2 )
      | ~ ( r2_hidden @ sk_C_1 @ X41 )
      | ~ ( r2_hidden @ sk_B @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['158'])).

thf('160',plain,(
    r2_hidden @ sk_B @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['84','86','87','88','2','78','143','152','159'])).

thf('161',plain,(
    r2_hidden @ sk_B @ sk_D_2 ),
    inference(simpl_trail,[status(thm)],['157','160'])).

thf('162',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v6_orders_2 @ sk_D_2 @ sk_A )
   <= ( v6_orders_2 @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('166',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['85'])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('167',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v6_orders_2 @ X8 @ X9 )
      | ( r7_relat_2 @ ( u1_orders_2 @ X9 ) @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('168',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_D_2 )
      | ~ ( v6_orders_2 @ sk_D_2 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_D_2 )
      | ~ ( v6_orders_2 @ sk_D_2 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_D_2 )
   <= ( ( v6_orders_2 @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['165','170'])).

thf(d7_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r7_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ~ ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) )).

thf('172',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r7_relat_2 @ X17 @ X18 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X19 ) @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X17 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('173',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_D_2 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ sk_D_2 ) )
   <= ( ( v6_orders_2 @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_D_2 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ sk_D_2 ) )
   <= ( ( v6_orders_2 @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['164','173'])).

thf('175',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D_2 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
        | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ sk_D_2 ) )
   <= ( ( v6_orders_2 @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v6_orders_2 @ sk_D_2 @ sk_A )
    | ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['62'])).

thf('178',plain,(
    v6_orders_2 @ sk_D_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['84','86','87','88','2','78','143','152','177'])).

thf('179',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ sk_C_1 @ X41 )
      | ~ ( r2_hidden @ sk_B @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['179'])).

thf('181',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['84','86','87','88','2','78','143','152','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['176','178','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['161','182'])).

thf('184',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','183'])).

thf('185',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( u1_orders_2 @ X22 ) )
      | ( r1_orders_2 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('186',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    ! [X41: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ~ ( r2_hidden @ sk_C_1 @ X41 )
      | ~ ( r2_hidden @ sk_B @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['191'])).

thf('193',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ! [X41: $i] :
        ( ~ ( r2_hidden @ sk_C_1 @ X41 )
        | ~ ( r2_hidden @ sk_B @ X41 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v6_orders_2 @ X41 @ sk_A ) ) ),
    inference(split,[status(esa)],['191'])).

thf('194',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['84','86','87','88','2','78','143','152','193'])).

thf('195',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['192','194'])).

thf('196',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(clc,[status(thm)],['190','195'])).

thf('197',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( u1_orders_2 @ X22 ) )
      | ( r1_orders_2 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('198',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('203',plain,(
    $false ),
    inference(demod,[status(thm)],['80','202'])).


%------------------------------------------------------------------------------
