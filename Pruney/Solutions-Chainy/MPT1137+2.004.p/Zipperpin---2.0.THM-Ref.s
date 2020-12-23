%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NW1xKDhFIT

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 315 expanded)
%              Number of leaves         :   32 ( 103 expanded)
%              Depth                    :   21
%              Number of atoms          :  691 (3939 expanded)
%              Number of equality atoms :   14 ( 118 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t25_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( r1_orders_2 @ A @ B @ C )
                    & ( r1_orders_2 @ A @ C @ B ) )
                 => ( B = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d6_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v5_orders_2 @ A )
      <=> ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i] :
      ( ~ ( v5_orders_2 @ X21 )
      | ( r4_relat_2 @ ( u1_orders_2 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X25: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_orders_2 @ X23 @ X22 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ ( u1_orders_2 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d4_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r4_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) )
             => ( C = D ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r4_relat_2 @ X17 @ X18 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X19 ) @ X17 )
      | ( X19 = X20 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_B_1 = sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_orders_2 @ X23 @ X22 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ ( u1_orders_2 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_B_1 = sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','42'])).

thf('44',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','42'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('49',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','42'])).

thf('50',plain,(
    ! [X25: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_xboole_0 @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,
    ( ( u1_orders_2 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','57'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('60',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    $false ),
    inference('sup-',[status(thm)],['47','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NW1xKDhFIT
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 101 iterations in 0.046s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(t25_orders_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.20/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                  ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.20/0.50                    ( ( B ) = ( C ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t25_orders_2])).
% 0.20/0.50  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t2_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((r2_hidden @ X4 @ X5)
% 0.20/0.50          | (v1_xboole_0 @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(d6_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ A ) =>
% 0.20/0.50       ( ( v5_orders_2 @ A ) <=>
% 0.20/0.50         ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X21 : $i]:
% 0.20/0.50         (~ (v5_orders_2 @ X21)
% 0.20/0.50          | (r4_relat_2 @ (u1_orders_2 @ X21) @ (u1_struct_0 @ X21))
% 0.20/0.50          | ~ (l1_orders_2 @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [d6_orders_2])).
% 0.20/0.50  thf(dt_u1_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ A ) =>
% 0.20/0.50       ( m1_subset_1 @
% 0.20/0.50         ( u1_orders_2 @ A ) @ 
% 0.20/0.50         ( k1_zfmisc_1 @
% 0.20/0.50           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X25 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (u1_orders_2 @ X25) @ 
% 0.20/0.50           (k1_zfmisc_1 @ 
% 0.20/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X25))))
% 0.20/0.50          | ~ (l1_orders_2 @ X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.50          | (v1_relat_1 @ X9)
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ 
% 0.20/0.50               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.20/0.50          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d9_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.20/0.50                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.20/0.50          | ~ (r1_orders_2 @ X23 @ X22 @ X24)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X22 @ X24) @ (u1_orders_2 @ X23))
% 0.20/0.50          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.50          | ~ (l1_orders_2 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((~ (r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.20/0.50        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.50  thf('16', plain, ((r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf(d4_relat_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( r4_relat_2 @ A @ B ) <=>
% 0.20/0.50           ( ![C:$i,D:$i]:
% 0.20/0.50             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.20/0.50                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.20/0.50                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) =>
% 0.20/0.50               ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (r4_relat_2 @ X17 @ X18)
% 0.20/0.50          | ~ (r2_hidden @ X19 @ X18)
% 0.20/0.50          | ~ (r2_hidden @ X20 @ X18)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X17)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X20 @ X19) @ X17)
% 0.20/0.50          | ((X19) = (X20))
% 0.20/0.50          | ~ (v1_relat_1 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.50          | ((sk_B_1) = (sk_C_1))
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B_1) @ (u1_orders_2 @ sk_A))
% 0.20/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.20/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.20/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.20/0.50          | ~ (r1_orders_2 @ X23 @ X22 @ X24)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X22 @ X24) @ (u1_orders_2 @ X23))
% 0.20/0.50          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.50          | ~ (l1_orders_2 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B_1)
% 0.20/0.50        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B_1) @ (u1_orders_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '25'])).
% 0.20/0.50  thf('27', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B_1) @ (u1_orders_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.50          | ((sk_B_1) = (sk_C_1))
% 0.20/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.20/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.20/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '28'])).
% 0.20/0.50  thf('30', plain, (((sk_B_1) != (sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.20/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.20/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.20/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.20/0.50          | ~ (r2_hidden @ sk_C_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '31'])).
% 0.20/0.50  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.20/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.20/0.50          | ~ (r2_hidden @ sk_C_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.50        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '34'])).
% 0.20/0.50  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '38'])).
% 0.20/0.50  thf('40', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((r2_hidden @ X4 @ X5)
% 0.20/0.50          | (v1_xboole_0 @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['39', '42'])).
% 0.20/0.50  thf('44', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['39', '42'])).
% 0.20/0.50  thf(l13_xboole_0, axiom,
% 0.20/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.50  thf('46', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('49', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['39', '42'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X25 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (u1_orders_2 @ X25) @ 
% 0.20/0.50           (k1_zfmisc_1 @ 
% 0.20/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X25))))
% 0.20/0.50          | ~ (l1_orders_2 @ X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.50  thf(cc4_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.50           ( v1_xboole_0 @ C ) ) ) ))).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X13)
% 0.20/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 0.20/0.50          | (v1_xboole_0 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ X0)
% 0.20/0.50          | (v1_xboole_0 @ (u1_orders_2 @ X0))
% 0.20/0.50          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_orders_2 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['49', '52'])).
% 0.20/0.50  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('55', plain, ((v1_xboole_0 @ (u1_orders_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.50  thf('57', plain, (((u1_orders_2 @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain, ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ k1_xboole_0)),
% 0.20/0.50      inference('demod', [status(thm)], ['48', '57'])).
% 0.20/0.50  thf(rc3_subset_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ?[B:$i]:
% 0.20/0.50       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.20/0.50  thf(cc1_subset_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.20/0.50          | (v1_xboole_0 @ X1)
% 0.20/0.50          | ~ (v1_xboole_0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.50          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf(t5_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.50          | ~ (v1_xboole_0 @ X8)
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ X0)
% 0.20/0.50          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.50  thf('69', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '68'])).
% 0.20/0.50  thf('70', plain, ($false), inference('sup-', [status(thm)], ['47', '69'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
