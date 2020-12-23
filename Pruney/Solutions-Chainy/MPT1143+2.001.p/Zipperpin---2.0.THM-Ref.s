%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Br0CTZ0JYM

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:37 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 167 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  802 (1890 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X5 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r7_relat_2 @ ( u1_orders_2 @ X14 ) @ X13 )
      | ( v6_orders_2 @ X13 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v6_orders_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v6_orders_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( ( k6_domain_1 @ X27 @ X28 )
        = ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ~ ( v6_orders_2 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('18',plain,
    ( ( ~ ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('22',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('24',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('30',plain,(
    ~ ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v6_orders_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['15','30'])).

thf('32',plain,
    ( ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','31'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X26: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_orders_2 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( u1_orders_2 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( r1_orders_2 @ X30 @ X29 @ X29 )
      | ~ ( l1_orders_2 @ X30 )
      | ~ ( v3_orders_2 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['42','50'])).

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

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_D @ X15 @ X16 ) @ X15 )
      | ( r7_relat_2 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('54',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 @ X16 ) @ X15 )
      | ( r7_relat_2 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('57',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X15 @ X16 ) @ ( sk_D @ X15 @ X16 ) ) @ X16 )
      | ( r7_relat_2 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r7_relat_2 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','63'])).

thf('65',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','67'])).

thf('69',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('72',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Br0CTZ0JYM
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 137 iterations in 0.096s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.59  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.40/0.59  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(r7_relat_2_type, type, r7_relat_2: $i > $i > $o).
% 0.40/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.40/0.59  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.59  thf(t35_orders_2, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.59           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.40/0.59             ( m1_subset_1 @
% 0.40/0.59               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.40/0.59               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.40/0.59            ( l1_orders_2 @ A ) ) =>
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.59              ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.40/0.59                ( m1_subset_1 @
% 0.40/0.59                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.40/0.59                  ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t35_orders_2])).
% 0.40/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t2_subset, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.40/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i]:
% 0.40/0.59         ((r2_hidden @ X7 @ X8)
% 0.40/0.59          | (v1_xboole_0 @ X8)
% 0.40/0.59          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf(t63_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r2_hidden @ A @ B ) =>
% 0.40/0.59       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i]:
% 0.40/0.59         ((m1_subset_1 @ (k1_tarski @ X5) @ (k1_zfmisc_1 @ X6))
% 0.40/0.59          | ~ (r2_hidden @ X5 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.59  thf(d11_orders_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_orders_2 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59           ( ( v6_orders_2 @ B @ A ) <=>
% 0.40/0.59             ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) ))).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X13 : $i, X14 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.40/0.59          | ~ (r7_relat_2 @ (u1_orders_2 @ X14) @ X13)
% 0.40/0.59          | (v6_orders_2 @ X13 @ X14)
% 0.40/0.59          | ~ (l1_orders_2 @ X14))),
% 0.40/0.59      inference('cnf', [status(esa)], [d11_orders_2])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | ~ (l1_orders_2 @ sk_A)
% 0.40/0.59        | (v6_orders_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.59        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.59  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v6_orders_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.59        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.40/0.59  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k6_domain_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.40/0.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X27 : $i, X28 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X27)
% 0.40/0.59          | ~ (m1_subset_1 @ X28 @ X27)
% 0.40/0.59          | ((k6_domain_1 @ X27 @ X28) = (k1_tarski @ X28)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      ((~ (v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.59        | ~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      ((~ (v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.40/0.59         <= (~
% 0.40/0.59             ((v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.40/0.59      inference('split', [status(esa)], ['13'])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (((~ (v6_orders_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.59         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.59         <= (~
% 0.40/0.59             ((v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['12', '14'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      ((~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.40/0.59         <= (~
% 0.40/0.59             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('split', [status(esa)], ['13'])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (((~ (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.40/0.59            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.59         <= (~
% 0.40/0.59             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59         <= (~
% 0.40/0.59             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('clc', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf(fc2_struct_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.59       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X12 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.40/0.59          | ~ (l1_struct_0 @ X12)
% 0.40/0.59          | (v2_struct_0 @ X12))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.59         <= (~
% 0.40/0.59             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_l1_orders_2, axiom,
% 0.40/0.59    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_orders_2 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.40/0.59  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A))
% 0.40/0.59         <= (~
% 0.40/0.59             ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('demod', [status(thm)], ['22', '25'])).
% 0.40/0.59  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (~ ((v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.40/0.59       ~
% 0.40/0.59       ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('split', [status(esa)], ['13'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (~ ((v6_orders_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.40/0.59      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      ((~ (v6_orders_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['15', '30'])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      ((~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('clc', [status(thm)], ['9', '31'])).
% 0.40/0.59  thf(dt_u1_orders_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_orders_2 @ A ) =>
% 0.40/0.59       ( m1_subset_1 @
% 0.40/0.59         ( u1_orders_2 @ A ) @ 
% 0.40/0.59         ( k1_zfmisc_1 @
% 0.40/0.59           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X26 : $i]:
% 0.40/0.59         ((m1_subset_1 @ (u1_orders_2 @ X26) @ 
% 0.40/0.59           (k1_zfmisc_1 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X26))))
% 0.40/0.59          | ~ (l1_orders_2 @ X26))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.40/0.59  thf(cc1_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( v1_relat_1 @ C ) ))).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.59         ((v1_relat_1 @ X9)
% 0.40/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d9_orders_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_orders_2 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.59               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.40/0.59                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.40/0.59          | ~ (r1_orders_2 @ X21 @ X20 @ X22)
% 0.40/0.59          | (r2_hidden @ (k4_tarski @ X20 @ X22) @ (u1_orders_2 @ X21))
% 0.40/0.59          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.40/0.59          | ~ (l1_orders_2 @ X21))),
% 0.40/0.59      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_orders_2 @ sk_A)
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 0.40/0.59          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.59  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 0.40/0.59          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.40/0.59        | (r2_hidden @ (k4_tarski @ sk_B @ sk_B) @ (u1_orders_2 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['36', '41'])).
% 0.40/0.59  thf('43', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t24_orders_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.59           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X29 : $i, X30 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.40/0.59          | (r1_orders_2 @ X30 @ X29 @ X29)
% 0.40/0.59          | ~ (l1_orders_2 @ X30)
% 0.40/0.59          | ~ (v3_orders_2 @ X30)
% 0.40/0.59          | (v2_struct_0 @ X30))),
% 0.40/0.59      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v3_orders_2 @ sk_A)
% 0.40/0.59        | ~ (l1_orders_2 @ sk_A)
% 0.40/0.59        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.59  thf('46', plain, ((v3_orders_2 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.40/0.59  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('50', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.40/0.59      inference('clc', [status(thm)], ['48', '49'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      ((r2_hidden @ (k4_tarski @ sk_B @ sk_B) @ (u1_orders_2 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '50'])).
% 0.40/0.59  thf(d7_relat_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( r7_relat_2 @ A @ B ) <=>
% 0.40/0.59           ( ![C:$i,D:$i]:
% 0.40/0.59             ( ~( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.40/0.59                  ( ~( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) & 
% 0.40/0.59                  ( ~( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X15 : $i, X16 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_D @ X15 @ X16) @ X15)
% 0.40/0.59          | (r7_relat_2 @ X16 @ X15)
% 0.40/0.59          | ~ (v1_relat_1 @ X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [d7_relat_2])).
% 0.40/0.59  thf(d1_tarski, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (![X0 : $i, X3 : $i]:
% 0.40/0.59         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['53'])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X1)
% 0.40/0.59          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ((sk_D @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['52', '54'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X15 : $i, X16 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_C_1 @ X15 @ X16) @ X15)
% 0.40/0.59          | (r7_relat_2 @ X16 @ X15)
% 0.40/0.59          | ~ (v1_relat_1 @ X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [d7_relat_2])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      (![X0 : $i, X3 : $i]:
% 0.40/0.59         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['53'])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X1)
% 0.40/0.59          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      (![X15 : $i, X16 : $i]:
% 0.40/0.59         (~ (r2_hidden @ 
% 0.40/0.59             (k4_tarski @ (sk_C_1 @ X15 @ X16) @ (sk_D @ X15 @ X16)) @ X16)
% 0.40/0.59          | (r7_relat_2 @ X16 @ X15)
% 0.40/0.59          | ~ (v1_relat_1 @ X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [d7_relat_2])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ (k4_tarski @ X0 @ (sk_D @ (k1_tarski @ X0) @ X1)) @ X1)
% 0.40/0.59          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X1)
% 0.40/0.59          | ~ (v1_relat_1 @ X1)
% 0.40/0.59          | (r7_relat_2 @ X1 @ (k1_tarski @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X1)
% 0.40/0.59          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (r2_hidden @ (k4_tarski @ X0 @ (sk_D @ (k1_tarski @ X0) @ X1)) @ 
% 0.40/0.59               X1))),
% 0.40/0.59      inference('simplify', [status(thm)], ['60'])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 0.40/0.59          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X1)
% 0.40/0.59          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['55', '61'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X1)
% 0.40/0.59          | (r7_relat_2 @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1))),
% 0.40/0.59      inference('simplify', [status(thm)], ['62'])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (((r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B))
% 0.40/0.59        | ~ (v1_relat_1 @ (u1_orders_2 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['51', '63'])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      ((~ (l1_orders_2 @ sk_A)
% 0.40/0.59        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['35', '64'])).
% 0.40/0.59  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('67', plain, ((r7_relat_2 @ (u1_orders_2 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.59  thf('68', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['32', '67'])).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      (![X12 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.40/0.59          | ~ (l1_struct_0 @ X12)
% 0.40/0.59          | (v2_struct_0 @ X12))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.59  thf('70', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['68', '69'])).
% 0.40/0.59  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf('72', plain, ((v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['70', '71'])).
% 0.40/0.59  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
