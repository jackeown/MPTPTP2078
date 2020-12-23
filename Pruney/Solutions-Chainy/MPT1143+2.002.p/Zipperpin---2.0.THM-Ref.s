%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B8zy65u9C5

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 170 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  860 (1832 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t35_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
            & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
              & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( l1_orders_2 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( ( k6_domain_1 @ X36 @ X37 )
        = ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ X32 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d4_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_orders_2 @ A )
      <=> ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X26: $i] :
      ( ~ ( v3_orders_2 @ X26 )
      | ( r1_relat_2 @ ( u1_orders_2 @ X26 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_orders_2])).

thf(d1_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_relat_2 @ A @ B )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
             => ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_relat_2 @ X20 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X22 ) @ X20 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

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

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X27 @ X28 ) @ X27 )
      | ( r7_relat_2 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('30',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('31',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X27 @ X28 ) @ X27 )
      | ( r7_relat_2 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('34',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X27 @ X28 ) @ ( sk_D_1 @ X27 @ X28 ) ) @ X28 )
      | ( r7_relat_2 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 ) ) @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ ( k1_tarski @ X0 ) @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r7_relat_2 @ ( u1_orders_2 @ X25 ) @ X24 )
      | ( v6_orders_2 @ X24 @ X25 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('53',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('56',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('62',plain,(
    ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['49','62'])).

thf('64',plain,
    ( ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','63'])).

thf('65',plain,
    ( ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','66'])).

thf('68',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('74',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B8zy65u9C5
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:56:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 157 iterations in 0.079s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.22/0.53  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.22/0.53  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.53  thf(r7_relat_2_type, type, r7_relat_2: $i > $i > $o).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(t35_orders_2, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.22/0.53             ( m1_subset_1 @
% 0.22/0.53               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.53               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.53            ( l1_orders_2 @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.54              ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.22/0.54                ( m1_subset_1 @
% 0.22/0.54                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.54                  ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t35_orders_2])).
% 0.22/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_u1_orders_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_orders_2 @ A ) =>
% 0.22/0.54       ( m1_subset_1 @
% 0.22/0.54         ( u1_orders_2 @ A ) @ 
% 0.22/0.54         ( k1_zfmisc_1 @
% 0.22/0.54           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X35 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (u1_orders_2 @ X35) @ 
% 0.22/0.54           (k1_zfmisc_1 @ 
% 0.22/0.54            (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X35))))
% 0.22/0.54          | ~ (l1_orders_2 @ X35))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.22/0.54  thf(cc2_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.22/0.54          | (v1_relat_1 @ X15)
% 0.22/0.54          | ~ (v1_relat_1 @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_orders_2 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ 
% 0.22/0.54               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.22/0.54          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf(fc6_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf(d1_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.54  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.54  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X36 : $i, X37 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X36)
% 0.22/0.54          | ~ (m1_subset_1 @ X37 @ X36)
% 0.22/0.54          | ((k6_domain_1 @ X36 @ X37) = (k1_tarski @ X37)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_k6_domain_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.54       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X32 : $i, X33 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X32)
% 0.22/0.54          | ~ (m1_subset_1 @ X33 @ X32)
% 0.22/0.54          | (m1_subset_1 @ (k6_domain_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.22/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['10', '13'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.54  thf(l3_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X12 @ X13)
% 0.22/0.54          | (r2_hidden @ X12 @ X14)
% 0.22/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.22/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (((r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf(d4_orders_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_orders_2 @ A ) =>
% 0.22/0.54       ( ( v3_orders_2 @ A ) <=>
% 0.22/0.54         ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X26 : $i]:
% 0.22/0.54         (~ (v3_orders_2 @ X26)
% 0.22/0.54          | (r1_relat_2 @ (u1_orders_2 @ X26) @ (u1_struct_0 @ X26))
% 0.22/0.54          | ~ (l1_orders_2 @ X26))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_orders_2])).
% 0.22/0.54  thf(d1_relat_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( r1_relat_2 @ A @ B ) <=>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( r2_hidden @ C @ B ) =>
% 0.22/0.54               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.54         (~ (r1_relat_2 @ X20 @ X21)
% 0.22/0.54          | (r2_hidden @ (k4_tarski @ X22 @ X22) @ X20)
% 0.22/0.54          | ~ (r2_hidden @ X22 @ X21)
% 0.22/0.54          | ~ (v1_relat_1 @ X20))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (l1_orders_2 @ X0)
% 0.22/0.54          | ~ (v3_orders_2 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 0.22/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.54          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (l1_orders_2 @ X0)
% 0.22/0.54          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.22/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (v3_orders_2 @ X0)
% 0.22/0.54          | ~ (l1_orders_2 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v3_orders_2 @ X0)
% 0.22/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.54          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.22/0.54          | ~ (l1_orders_2 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.54        | (r2_hidden @ (k4_tarski @ sk_B @ sk_B) @ (u1_orders_2 @ sk_A))
% 0.22/0.54        | ~ (v3_orders_2 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['18', '24'])).
% 0.22/0.54  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (r2_hidden @ (k4_tarski @ sk_B @ sk_B) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.54  thf(d7_relat_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( r7_relat_2 @ A @ B ) <=>
% 0.22/0.54           ( ![C:$i,D:$i]:
% 0.22/0.54             ( ~( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.22/0.54                  ( ~( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) & 
% 0.22/0.54                  ( ~( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X27 : $i, X28 : $i]:
% 0.22/0.54         ((r2_hidden @ (sk_D_1 @ X27 @ X28) @ X27)
% 0.22/0.54          | (r7_relat_2 @ X28 @ X27)
% 0.22/0.54          | ~ (v1_relat_1 @ X28))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_relat_2])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X0 : $i, X3 : $i]:
% 0.22/0.54         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X1)
% 0.22/0.54          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.22/0.54          | ((sk_D_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['29', '31'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X27 : $i, X28 : $i]:
% 0.22/0.54         ((r2_hidden @ (sk_C_2 @ X27 @ X28) @ X27)
% 0.22/0.54          | (r7_relat_2 @ X28 @ X27)
% 0.22/0.54          | ~ (v1_relat_1 @ X28))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_relat_2])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X0 : $i, X3 : $i]:
% 0.22/0.54         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X1)
% 0.22/0.54          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.22/0.54          | ((sk_C_2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X27 : $i, X28 : $i]:
% 0.22/0.54         (~ (r2_hidden @ 
% 0.22/0.54             (k4_tarski @ (sk_C_2 @ X27 @ X28) @ (sk_D_1 @ X27 @ X28)) @ X28)
% 0.22/0.54          | (r7_relat_2 @ X28 @ X27)
% 0.22/0.54          | ~ (v1_relat_1 @ X28))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_relat_2])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ (k1_tarski @ X0) @ X1)) @ 
% 0.22/0.54             X1)
% 0.22/0.54          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X1)
% 0.22/0.54          | ~ (v1_relat_1 @ X1)
% 0.22/0.54          | (r7_relat_2 @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X1)
% 0.22/0.54          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.22/0.54          | ~ (r2_hidden @ 
% 0.22/0.54               (k4_tarski @ X0 @ (sk_D_1 @ (k1_tarski @ X0) @ X1)) @ X1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 0.22/0.54          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X1)
% 0.22/0.54          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '38'])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X1)
% 0.22/0.54          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.22/0.54          | ~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.54        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['28', '40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf(d11_orders_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_orders_2 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v6_orders_2 @ B @ A ) <=>
% 0.22/0.54             ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) ))).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X24 : $i, X25 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.54          | ~ (r7_relat_2 @ (u1_orders_2 @ X25) @ X24)
% 0.22/0.54          | (v6_orders_2 @ X24 @ X25)
% 0.22/0.54          | ~ (l1_orders_2 @ X25))),
% 0.22/0.54      inference('cnf', [status(esa)], [d11_orders_2])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.54        | (v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.54        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ 
% 0.22/0.54             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('46', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.54        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ 
% 0.22/0.54             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      ((~ (v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.54        | ~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      ((~ (v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.22/0.54         <= (~
% 0.22/0.54             ((v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['48'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      ((~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.54         <= (~
% 0.22/0.54             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.54      inference('split', [status(esa)], ['48'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~
% 0.22/0.54             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.54  thf(fc2_struct_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      (![X23 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.22/0.54          | ~ (l1_struct_0 @ X23)
% 0.22/0.54          | (v2_struct_0 @ X23))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~
% 0.22/0.54             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.54  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_l1_orders_2, axiom,
% 0.22/0.54    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_orders_2 @ X34))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.54  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_A))
% 0.22/0.54         <= (~
% 0.22/0.54             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.54      inference('demod', [status(thm)], ['54', '57'])).
% 0.22/0.54  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      (~ ((v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.22/0.54       ~
% 0.22/0.54       ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['48'])).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      (~ ((v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (~ (v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['49', '62'])).
% 0.22/0.54  thf('64', plain,
% 0.22/0.54      ((~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ 
% 0.22/0.54           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('clc', [status(thm)], ['47', '63'])).
% 0.22/0.54  thf('65', plain,
% 0.22/0.54      ((~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['42', '64'])).
% 0.22/0.54  thf('66', plain,
% 0.22/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['65'])).
% 0.22/0.54  thf('67', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.22/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('clc', [status(thm)], ['41', '66'])).
% 0.22/0.54  thf('68', plain,
% 0.22/0.54      ((~ (l1_orders_2 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '67'])).
% 0.22/0.54  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('70', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['68', '69'])).
% 0.22/0.54  thf('71', plain,
% 0.22/0.54      (![X23 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.22/0.54          | ~ (l1_struct_0 @ X23)
% 0.22/0.54          | (v2_struct_0 @ X23))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.54  thf('72', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.54  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.54  thf('74', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.54  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
