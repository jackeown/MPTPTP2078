%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5keJhkhspB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:48 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  120 (1047 expanded)
%              Number of leaves         :   27 ( 312 expanded)
%              Depth                    :   22
%              Number of atoms          :  786 (14355 expanded)
%              Number of equality atoms :   30 ( 160 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t48_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_orders_2])).

thf('0',plain,(
    r2_hidden @ sk_B_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_B_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
            & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t47_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( r2_hidden @ B @ C )
                  & ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ ( k1_orders_2 @ X19 @ X20 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_orders_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','29'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('32',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( k1_tarski @ X4 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','32'])).

thf('34',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['5','33'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['2','36'])).

thf('38',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','32'])).

thf('39',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(dt_k1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_orders_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_orders_2])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','58'])).

thf('60',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('61',plain,(
    r2_hidden @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('64',plain,(
    r2_hidden @ ( k6_domain_1 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('65',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('66',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('67',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ( k6_domain_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ ( k1_orders_2 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('72',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('73',plain,(
    m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('75',plain,
    ( ( k6_domain_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','68'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('77',plain,(
    m1_subset_1 @ ( k1_orders_2 @ sk_A @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k1_orders_2 @ sk_A @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('81',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( k1_tarski @ X4 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    r2_hidden @ ( k1_orders_2 @ sk_A @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('87',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['5','33'])).

thf('89',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['70','87','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5keJhkhspB
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:48:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 178 iterations in 0.162s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.45/0.65  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.65  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.65  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.45/0.65  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.45/0.65  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.45/0.65  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(t48_orders_2, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.65         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ~( r2_hidden @
% 0.45/0.65                B @ 
% 0.45/0.65                ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.65            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65              ( ~( r2_hidden @
% 0.45/0.65                   B @ 
% 0.45/0.65                   ( k1_orders_2 @
% 0.45/0.65                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t48_orders_2])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      ((r2_hidden @ sk_B_1 @ 
% 0.45/0.65        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d1_xboole_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (~ (v1_xboole_0 @ 
% 0.45/0.65          (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.65  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d2_subset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X11 @ X10)
% 0.45/0.65          | (v1_xboole_0 @ X11)
% 0.45/0.65          | ~ (v1_xboole_0 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.65  thf('6', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k6_domain_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.45/0.65       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ X14)
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ X14)
% 0.45/0.65          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.45/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      ((r2_hidden @ sk_B_1 @ 
% 0.45/0.65        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('10', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t35_orders_2, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.45/0.65             ( m1_subset_1 @
% 0.45/0.65               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.45/0.65               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.45/0.65          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X16) @ 
% 0.45/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.65          | ~ (l1_orders_2 @ X17)
% 0.45/0.65          | ~ (v3_orders_2 @ X17)
% 0.45/0.65          | (v2_struct_0 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v3_orders_2 @ sk_A)
% 0.45/0.65        | ~ (l1_orders_2 @ sk_A)
% 0.45/0.65        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.45/0.65  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf(t47_orders_2, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.65         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65               ( ~( ( r2_hidden @ B @ C ) & 
% 0.45/0.65                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.45/0.65          | ~ (r2_hidden @ X18 @ (k1_orders_2 @ X19 @ X20))
% 0.45/0.65          | ~ (r2_hidden @ X18 @ X20)
% 0.45/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | ~ (l1_orders_2 @ X19)
% 0.45/0.65          | ~ (v5_orders_2 @ X19)
% 0.45/0.65          | ~ (v4_orders_2 @ X19)
% 0.45/0.65          | ~ (v3_orders_2 @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [t47_orders_2])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v3_orders_2 @ sk_A)
% 0.45/0.65          | ~ (v4_orders_2 @ sk_A)
% 0.45/0.65          | ~ (v5_orders_2 @ sk_A)
% 0.45/0.65          | ~ (l1_orders_2 @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.45/0.65          | ~ (r2_hidden @ X0 @ 
% 0.45/0.65               (k1_orders_2 @ sk_A @ 
% 0.45/0.65                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.45/0.65          | ~ (r2_hidden @ X0 @ 
% 0.45/0.65               (k1_orders_2 @ sk_A @ 
% 0.45/0.65                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (r2_hidden @ sk_B_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '24'])).
% 0.45/0.65  thf('26', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      ((~ (r2_hidden @ sk_B_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.65  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (~ (r2_hidden @ sk_B_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.45/0.65      inference('clc', [status(thm)], ['27', '28'])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      ((~ (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_B_1))
% 0.45/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['8', '29'])).
% 0.45/0.65  thf(d1_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.65         (((X5) != (X4)) | (r2_hidden @ X5 @ X6) | ((X6) != (k1_tarski @ X4)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.65  thf('32', plain, (![X4 : $i]: (r2_hidden @ X4 @ (k1_tarski @ X4))),
% 0.45/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.65  thf('33', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['30', '32'])).
% 0.45/0.65  thf('34', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.45/0.65      inference('demod', [status(thm)], ['5', '33'])).
% 0.45/0.65  thf(l13_xboole_0, axiom,
% 0.45/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.65  thf('36', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (~ (v1_xboole_0 @ 
% 0.45/0.65          (k1_orders_2 @ sk_A @ 
% 0.45/0.65           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['2', '36'])).
% 0.45/0.65  thf('38', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['30', '32'])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.65  thf('40', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (~ (v1_xboole_0 @ 
% 0.45/0.65          (k1_orders_2 @ sk_A @ (k6_domain_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['37', '40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X9 : $i, X10 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X9 @ X10)
% 0.45/0.65          | (r2_hidden @ X9 @ X10)
% 0.45/0.65          | (v1_xboole_0 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | (r2_hidden @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf(dt_k1_orders_2, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.65         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.45/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65       ( m1_subset_1 @
% 0.45/0.65         ( k1_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i]:
% 0.45/0.65         (~ (l1_orders_2 @ X12)
% 0.45/0.65          | ~ (v5_orders_2 @ X12)
% 0.45/0.65          | ~ (v4_orders_2 @ X12)
% 0.45/0.65          | ~ (v3_orders_2 @ X12)
% 0.45/0.65          | (v2_struct_0 @ X12)
% 0.45/0.65          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.45/0.65          | (m1_subset_1 @ (k1_orders_2 @ X12 @ X13) @ 
% 0.45/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k1_orders_2])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (((m1_subset_1 @ 
% 0.45/0.65         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.45/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v3_orders_2 @ sk_A)
% 0.45/0.65        | ~ (v4_orders_2 @ sk_A)
% 0.45/0.65        | ~ (v5_orders_2 @ sk_A)
% 0.45/0.65        | ~ (l1_orders_2 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.65  thf('48', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('49', plain, ((v4_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('50', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      (((m1_subset_1 @ 
% 0.45/0.65         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.45/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.45/0.65  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      ((m1_subset_1 @ 
% 0.45/0.65        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['52', '53'])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X11 @ X10)
% 0.45/0.65          | (v1_xboole_0 @ X11)
% 0.45/0.65          | ~ (v1_xboole_0 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.65        | (v1_xboole_0 @ 
% 0.45/0.65           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      (~ (v1_xboole_0 @ 
% 0.45/0.65          (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.65  thf('58', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      ((r2_hidden @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['44', '58'])).
% 0.45/0.65  thf('60', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      ((r2_hidden @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('62', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('63', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      ((r2_hidden @ (k6_domain_1 @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.45/0.65        (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.45/0.65  thf(t1_zfmisc_1, axiom,
% 0.45/0.65    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.45/0.65  thf('65', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (![X4 : $i, X7 : $i]:
% 0.45/0.65         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['66'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.45/0.65          | ((X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['65', '67'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (((k6_domain_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '68'])).
% 0.45/0.65  thf('70', plain, (~ (v1_xboole_0 @ (k1_orders_2 @ sk_A @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['41', '69'])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      ((m1_subset_1 @ 
% 0.45/0.65        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['52', '53'])).
% 0.45/0.65  thf('72', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      ((m1_subset_1 @ 
% 0.45/0.65        (k1_orders_2 @ sk_A @ 
% 0.45/0.65         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)) @ 
% 0.45/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['71', '72'])).
% 0.45/0.65  thf('74', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      (((k6_domain_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '68'])).
% 0.45/0.65  thf('76', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('77', plain,
% 0.45/0.65      ((m1_subset_1 @ (k1_orders_2 @ sk_A @ k1_xboole_0) @ 
% 0.45/0.65        (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      (![X9 : $i, X10 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X9 @ X10)
% 0.45/0.65          | (r2_hidden @ X9 @ X10)
% 0.45/0.65          | (v1_xboole_0 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.45/0.65        | (r2_hidden @ (k1_orders_2 @ sk_A @ k1_xboole_0) @ 
% 0.45/0.65           (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.65  thf('80', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.65  thf('81', plain, (![X4 : $i]: (r2_hidden @ X4 @ (k1_tarski @ X4))),
% 0.45/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.65  thf('82', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('83', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.65  thf('84', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['80', '83'])).
% 0.45/0.65  thf('85', plain,
% 0.45/0.65      ((r2_hidden @ (k1_orders_2 @ sk_A @ k1_xboole_0) @ 
% 0.45/0.65        (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('clc', [status(thm)], ['79', '84'])).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.45/0.65          | ((X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['65', '67'])).
% 0.45/0.65  thf('87', plain, (((k1_orders_2 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.65  thf('88', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.45/0.65      inference('demod', [status(thm)], ['5', '33'])).
% 0.45/0.65  thf('89', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['88', '89'])).
% 0.45/0.65  thf('91', plain, ($false),
% 0.45/0.65      inference('demod', [status(thm)], ['70', '87', '90'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
