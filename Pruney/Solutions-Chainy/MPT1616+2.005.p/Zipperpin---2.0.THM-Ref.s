%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sn7jxZjGCu

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:20 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 131 expanded)
%              Number of leaves         :   47 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  582 ( 986 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ~ ( v2_pre_topc @ X42 )
      | ( r2_hidden @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ ( k1_zfmisc_1 @ ( k3_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( m1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X45: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X45 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X42: $i] :
      ( ~ ( v2_pre_topc @ X42 )
      | ( r2_hidden @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('24',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X46 ) @ X46 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X46 ) )
        = ( k3_tarski @ X46 ) )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X46: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X46 ) )
        = ( k3_tarski @ X46 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X46 ) @ X46 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t24_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_1])).

thf('30',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('31',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('34',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('38',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sn7jxZjGCu
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/0.99  % Solved by: fo/fo7.sh
% 0.81/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/0.99  % done 627 iterations in 0.542s
% 0.81/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/0.99  % SZS output start Refutation
% 0.81/0.99  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.81/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/0.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.81/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.81/0.99  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.81/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.81/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.81/0.99  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.81/0.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.81/0.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.81/0.99  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.81/0.99  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.81/0.99  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.81/0.99  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.81/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.81/0.99  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.81/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.81/0.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.81/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/0.99  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.81/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/0.99  thf(d1_pre_topc, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( l1_pre_topc @ A ) =>
% 0.81/0.99       ( ( v2_pre_topc @ A ) <=>
% 0.81/0.99         ( ( ![B:$i]:
% 0.81/0.99             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/0.99               ( ![C:$i]:
% 0.81/0.99                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/0.99                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.81/0.99                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.81/0.99                     ( r2_hidden @
% 0.81/0.99                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.81/0.99                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.81/0.99           ( ![B:$i]:
% 0.81/0.99             ( ( m1_subset_1 @
% 0.81/0.99                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/0.99               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.81/0.99                 ( r2_hidden @
% 0.81/0.99                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.81/0.99                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.81/0.99           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.81/0.99  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.81/0.99  thf(zf_stmt_1, axiom,
% 0.81/0.99    (![B:$i,A:$i]:
% 0.81/0.99     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.81/0.99       ( ( m1_subset_1 @
% 0.81/0.99           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/0.99         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.81/0.99  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.81/0.99  thf(zf_stmt_3, axiom,
% 0.81/0.99    (![B:$i,A:$i]:
% 0.81/0.99     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.81/0.99       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.81/0.99         ( r2_hidden @
% 0.81/0.99           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.81/0.99  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.81/0.99  thf(zf_stmt_5, axiom,
% 0.81/0.99    (![B:$i,A:$i]:
% 0.81/0.99     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.81/0.99       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/0.99         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.81/0.99  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.81/0.99  thf(zf_stmt_7, axiom,
% 0.81/0.99    (![C:$i,B:$i,A:$i]:
% 0.81/0.99     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.81/0.99       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.81/0.99         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.81/0.99  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.81/0.99  thf(zf_stmt_9, axiom,
% 0.81/0.99    (![C:$i,B:$i,A:$i]:
% 0.81/0.99     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.81/0.99       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.81/0.99         ( r2_hidden @
% 0.81/0.99           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.81/0.99  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.81/0.99  thf(zf_stmt_11, axiom,
% 0.81/0.99    (![C:$i,B:$i,A:$i]:
% 0.81/0.99     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.81/0.99       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.81/0.99         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.81/0.99  thf(zf_stmt_12, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( l1_pre_topc @ A ) =>
% 0.81/0.99       ( ( v2_pre_topc @ A ) <=>
% 0.81/0.99         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.81/0.99           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.81/0.99           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.81/0.99  thf('0', plain,
% 0.81/0.99      (![X42 : $i]:
% 0.81/0.99         (~ (v2_pre_topc @ X42)
% 0.81/0.99          | (r2_hidden @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))
% 0.81/0.99          | ~ (l1_pre_topc @ X42))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.81/0.99  thf(t100_zfmisc_1, axiom,
% 0.81/0.99    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.81/0.99  thf('1', plain,
% 0.81/0.99      (![X10 : $i]: (r1_tarski @ X10 @ (k1_zfmisc_1 @ (k3_tarski @ X10)))),
% 0.81/0.99      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.81/0.99  thf(d3_tarski, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( r1_tarski @ A @ B ) <=>
% 0.81/0.99       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.81/0.99  thf('2', plain,
% 0.81/0.99      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.81/0.99         (~ (r2_hidden @ X3 @ X4)
% 0.81/0.99          | (r2_hidden @ X3 @ X5)
% 0.81/0.99          | ~ (r1_tarski @ X4 @ X5))),
% 0.81/0.99      inference('cnf', [status(esa)], [d3_tarski])).
% 0.81/0.99  thf('3', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]:
% 0.81/0.99         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 0.81/0.99          | ~ (r2_hidden @ X1 @ X0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['1', '2'])).
% 0.81/0.99  thf('4', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (l1_pre_topc @ X0)
% 0.81/0.99          | ~ (v2_pre_topc @ X0)
% 0.81/0.99          | (r2_hidden @ (u1_struct_0 @ X0) @ 
% 0.81/0.99             (k1_zfmisc_1 @ (k3_tarski @ (u1_pre_topc @ X0)))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['0', '3'])).
% 0.81/0.99  thf(d2_subset_1, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( ( v1_xboole_0 @ A ) =>
% 0.81/0.99         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.81/0.99       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.81/0.99         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.81/0.99  thf('5', plain,
% 0.81/0.99      (![X14 : $i, X15 : $i]:
% 0.81/0.99         (~ (r2_hidden @ X14 @ X15)
% 0.81/0.99          | (m1_subset_1 @ X14 @ X15)
% 0.81/0.99          | (v1_xboole_0 @ X15))),
% 0.81/0.99      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.81/0.99  thf(d1_xboole_0, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.81/0.99  thf('6', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.81/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.81/0.99  thf('7', plain,
% 0.81/0.99      (![X14 : $i, X15 : $i]:
% 0.81/0.99         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.81/0.99      inference('clc', [status(thm)], ['5', '6'])).
% 0.81/0.99  thf('8', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (v2_pre_topc @ X0)
% 0.81/0.99          | ~ (l1_pre_topc @ X0)
% 0.81/0.99          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.81/0.99             (k1_zfmisc_1 @ (k3_tarski @ (u1_pre_topc @ X0)))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['4', '7'])).
% 0.81/0.99  thf(t3_subset, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.81/0.99  thf('9', plain,
% 0.81/0.99      (![X17 : $i, X18 : $i]:
% 0.81/0.99         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.81/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/0.99  thf('10', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (l1_pre_topc @ X0)
% 0.81/0.99          | ~ (v2_pre_topc @ X0)
% 0.81/0.99          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['8', '9'])).
% 0.81/0.99  thf(dt_u1_pre_topc, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( l1_pre_topc @ A ) =>
% 0.81/0.99       ( m1_subset_1 @
% 0.81/0.99         ( u1_pre_topc @ A ) @ 
% 0.81/0.99         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.81/0.99  thf('11', plain,
% 0.81/0.99      (![X45 : $i]:
% 0.81/0.99         ((m1_subset_1 @ (u1_pre_topc @ X45) @ 
% 0.81/0.99           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45))))
% 0.81/0.99          | ~ (l1_pre_topc @ X45))),
% 0.81/0.99      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.81/0.99  thf('12', plain,
% 0.81/0.99      (![X17 : $i, X18 : $i]:
% 0.81/0.99         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.81/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/0.99  thf('13', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (l1_pre_topc @ X0)
% 0.81/0.99          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.81/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['11', '12'])).
% 0.81/0.99  thf(t95_zfmisc_1, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( r1_tarski @ A @ B ) =>
% 0.81/0.99       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.81/0.99  thf('14', plain,
% 0.81/0.99      (![X11 : $i, X12 : $i]:
% 0.81/0.99         ((r1_tarski @ (k3_tarski @ X11) @ (k3_tarski @ X12))
% 0.81/0.99          | ~ (r1_tarski @ X11 @ X12))),
% 0.81/0.99      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.81/0.99  thf('15', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (l1_pre_topc @ X0)
% 0.81/0.99          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.81/0.99             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/0.99  thf(t99_zfmisc_1, axiom,
% 0.81/0.99    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.81/0.99  thf('16', plain, (![X13 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X13)) = (X13))),
% 0.81/0.99      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.81/0.99  thf('17', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (l1_pre_topc @ X0)
% 0.81/0.99          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.81/0.99      inference('demod', [status(thm)], ['15', '16'])).
% 0.81/0.99  thf(d10_xboole_0, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/0.99  thf('18', plain,
% 0.81/0.99      (![X7 : $i, X9 : $i]:
% 0.81/0.99         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.81/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/0.99  thf('19', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (l1_pre_topc @ X0)
% 0.81/0.99          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.81/0.99               (k3_tarski @ (u1_pre_topc @ X0)))
% 0.81/0.99          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['17', '18'])).
% 0.81/0.99  thf('20', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (v2_pre_topc @ X0)
% 0.81/0.99          | ~ (l1_pre_topc @ X0)
% 0.81/0.99          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.81/0.99          | ~ (l1_pre_topc @ X0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['10', '19'])).
% 0.81/0.99  thf('21', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.81/0.99          | ~ (l1_pre_topc @ X0)
% 0.81/0.99          | ~ (v2_pre_topc @ X0))),
% 0.81/0.99      inference('simplify', [status(thm)], ['20'])).
% 0.81/0.99  thf('22', plain,
% 0.81/0.99      (![X42 : $i]:
% 0.81/0.99         (~ (v2_pre_topc @ X42)
% 0.81/0.99          | (r2_hidden @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42))
% 0.81/0.99          | ~ (l1_pre_topc @ X42))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.81/0.99  thf('23', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.81/0.99          | ~ (l1_pre_topc @ X0)
% 0.81/0.99          | ~ (v2_pre_topc @ X0))),
% 0.81/0.99      inference('simplify', [status(thm)], ['20'])).
% 0.81/0.99  thf(t14_yellow_1, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.81/0.99       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.81/0.99         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.81/0.99  thf('24', plain,
% 0.81/0.99      (![X46 : $i]:
% 0.81/0.99         (~ (r2_hidden @ (k3_tarski @ X46) @ X46)
% 0.81/0.99          | ((k4_yellow_0 @ (k2_yellow_1 @ X46)) = (k3_tarski @ X46))
% 0.81/0.99          | (v1_xboole_0 @ X46))),
% 0.81/0.99      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.81/0.99  thf('25', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.81/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.81/0.99  thf('26', plain,
% 0.81/0.99      (![X46 : $i]:
% 0.81/0.99         (((k4_yellow_0 @ (k2_yellow_1 @ X46)) = (k3_tarski @ X46))
% 0.81/0.99          | ~ (r2_hidden @ (k3_tarski @ X46) @ X46))),
% 0.81/0.99      inference('clc', [status(thm)], ['24', '25'])).
% 0.81/0.99  thf('27', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.81/0.99          | ~ (v2_pre_topc @ X0)
% 0.81/0.99          | ~ (l1_pre_topc @ X0)
% 0.81/0.99          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.81/0.99              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['23', '26'])).
% 0.81/0.99  thf('28', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (l1_pre_topc @ X0)
% 0.81/0.99          | ~ (v2_pre_topc @ X0)
% 0.81/0.99          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.81/0.99              = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.81/0.99          | ~ (l1_pre_topc @ X0)
% 0.81/0.99          | ~ (v2_pre_topc @ X0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['22', '27'])).
% 0.81/0.99  thf('29', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.81/0.99            = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.81/0.99          | ~ (v2_pre_topc @ X0)
% 0.81/0.99          | ~ (l1_pre_topc @ X0))),
% 0.81/0.99      inference('simplify', [status(thm)], ['28'])).
% 0.81/0.99  thf(t24_yellow_1, conjecture,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/0.99       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.81/0.99         ( u1_struct_0 @ A ) ) ))).
% 0.81/0.99  thf(zf_stmt_13, negated_conjecture,
% 0.81/0.99    (~( ![A:$i]:
% 0.81/0.99        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.81/0.99            ( l1_pre_topc @ A ) ) =>
% 0.81/0.99          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.81/0.99            ( u1_struct_0 @ A ) ) ) )),
% 0.81/0.99    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.81/0.99  thf('30', plain,
% 0.81/0.99      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.81/0.99         != (u1_struct_0 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.81/0.99  thf('31', plain,
% 0.81/0.99      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.81/0.99        | ~ (l1_pre_topc @ sk_A)
% 0.81/0.99        | ~ (v2_pre_topc @ sk_A))),
% 0.81/0.99      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/0.99  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.81/0.99  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.81/0.99  thf('34', plain,
% 0.81/0.99      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 0.81/0.99      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.81/0.99  thf('35', plain,
% 0.81/0.99      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.81/0.99        | ~ (v2_pre_topc @ sk_A)
% 0.81/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.81/0.99      inference('sup-', [status(thm)], ['21', '34'])).
% 0.81/0.99  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.81/0.99  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.81/0.99  thf('38', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.81/0.99      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.81/0.99  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.81/0.99  
% 0.81/0.99  % SZS output end Refutation
% 0.81/0.99  
% 0.81/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
