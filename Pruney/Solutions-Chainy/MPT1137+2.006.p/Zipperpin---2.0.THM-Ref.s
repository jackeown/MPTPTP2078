%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cRGFLKrIlU

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 132 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  597 (1570 expanded)
%              Number of equality atoms :    7 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d6_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v5_orders_2 @ A )
      <=> ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i] :
      ( ~ ( v5_orders_2 @ X18 )
      | ( r4_relat_2 @ ( u1_orders_2 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r4_relat_2 @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ X14 )
      | ( X16 = X17 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_B_1 = sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_B_1 = sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','47'])).

thf('49',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_xboole_0 @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['10','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cRGFLKrIlU
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 82 iterations in 0.043s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.21/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(t25_orders_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.21/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                  ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.21/0.50                    ( ( B ) = ( C ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t25_orders_2])).
% 0.21/0.50  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d9_orders_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.21/0.50                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.21/0.50          | ~ (r1_orders_2 @ X20 @ X19 @ X21)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.50          | ~ (l1_orders_2 @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.21/0.50        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.50  thf('7', plain, ((r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(d1_xboole_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf('10', plain, (~ (v1_xboole_0 @ (u1_orders_2 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d2_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X3 @ X4)
% 0.21/0.50          | (r2_hidden @ X3 @ X4)
% 0.21/0.50          | (v1_xboole_0 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X3 @ X4)
% 0.21/0.50          | (r2_hidden @ X3 @ X4)
% 0.21/0.50          | (v1_xboole_0 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf(d6_orders_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( ( v5_orders_2 @ A ) <=>
% 0.21/0.50         ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X18 : $i]:
% 0.21/0.50         (~ (v5_orders_2 @ X18)
% 0.21/0.50          | (r4_relat_2 @ (u1_orders_2 @ X18) @ (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (l1_orders_2 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [d6_orders_2])).
% 0.21/0.50  thf(dt_u1_orders_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( u1_orders_2 @ A ) @ 
% 0.21/0.50         ( k1_zfmisc_1 @
% 0.21/0.50           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X22 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 0.21/0.50           (k1_zfmisc_1 @ 
% 0.21/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 0.21/0.50          | ~ (l1_orders_2 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.50  thf(cc2_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.50          | (v1_relat_1 @ X6)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ 
% 0.21/0.50               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.21/0.50          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf(fc6_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(d4_relat_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( r4_relat_2 @ A @ B ) <=>
% 0.21/0.50           ( ![C:$i,D:$i]:
% 0.21/0.50             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.21/0.50                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.21/0.50                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) =>
% 0.21/0.50               ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         (~ (r4_relat_2 @ X14 @ X15)
% 0.21/0.50          | ~ (r2_hidden @ X16 @ X15)
% 0.21/0.50          | ~ (r2_hidden @ X17 @ X15)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X14)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X17 @ X16) @ X14)
% 0.21/0.50          | ((X16) = (X17))
% 0.21/0.50          | ~ (v1_relat_1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ((sk_B_1) = (sk_C_1))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B_1) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.21/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.21/0.50          | ~ (r1_orders_2 @ X20 @ X19 @ X21)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.50          | ~ (l1_orders_2 @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B_1)
% 0.21/0.50        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B_1) @ (u1_orders_2 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '31'])).
% 0.21/0.50  thf('33', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B_1) @ (u1_orders_2 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ((sk_B_1) = (sk_C_1))
% 0.21/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.21/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '34'])).
% 0.21/0.50  thf('36', plain, (((sk_B_1) != (sk_C_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.21/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_A)
% 0.21/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ sk_C_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '37'])).
% 0.21/0.50  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ sk_C_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.50        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.50        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '40'])).
% 0.21/0.50  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf('47', plain, (~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X22 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 0.21/0.50           (k1_zfmisc_1 @ 
% 0.21/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 0.21/0.50          | ~ (l1_orders_2 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.50  thf(cc4_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.50           ( v1_xboole_0 @ C ) ) ) ))).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ X10)
% 0.21/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.21/0.50          | (v1_xboole_0 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X0)
% 0.21/0.50          | (v1_xboole_0 @ (u1_orders_2 @ X0))
% 0.21/0.50          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_orders_2 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.50  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain, ((v1_xboole_0 @ (u1_orders_2 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain, ($false), inference('demod', [status(thm)], ['10', '54'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
