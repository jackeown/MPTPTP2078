%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TixAc6B1Hm

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:20 EST 2020

% Result     : Theorem 3.84s
% Output     : Refutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 124 expanded)
%              Number of leaves         :   47 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  588 ( 992 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ( r2_hidden @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k3_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X48 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X17 ) @ ( k3_tarski @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('14',plain,(
    ! [X19: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ( r2_hidden @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('22',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X49 ) @ X49 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X49 ) )
        = ( k3_tarski @ X49 ) )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X49: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X49 ) )
        = ( k3_tarski @ X49 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X49 ) @ X49 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

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

thf('28',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('29',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('32',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('36',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TixAc6B1Hm
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.84/4.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.84/4.03  % Solved by: fo/fo7.sh
% 3.84/4.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.84/4.03  % done 3116 iterations in 3.574s
% 3.84/4.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.84/4.03  % SZS output start Refutation
% 3.84/4.03  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.84/4.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.84/4.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.84/4.03  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 3.84/4.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.84/4.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.84/4.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.84/4.03  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 3.84/4.03  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 3.84/4.03  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 3.84/4.03  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 3.84/4.03  thf(sk_A_type, type, sk_A: $i).
% 3.84/4.03  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 3.84/4.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.84/4.03  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 3.84/4.03  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 3.84/4.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.84/4.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.84/4.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.84/4.03  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 3.84/4.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 3.84/4.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.84/4.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.84/4.03  thf(d1_pre_topc, axiom,
% 3.84/4.03    (![A:$i]:
% 3.84/4.03     ( ( l1_pre_topc @ A ) =>
% 3.84/4.03       ( ( v2_pre_topc @ A ) <=>
% 3.84/4.03         ( ( ![B:$i]:
% 3.84/4.03             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.84/4.03               ( ![C:$i]:
% 3.84/4.03                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.84/4.03                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 3.84/4.03                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 3.84/4.03                     ( r2_hidden @
% 3.84/4.03                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 3.84/4.03                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 3.84/4.03           ( ![B:$i]:
% 3.84/4.03             ( ( m1_subset_1 @
% 3.84/4.03                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.84/4.03               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 3.84/4.03                 ( r2_hidden @
% 3.84/4.03                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 3.84/4.03                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 3.84/4.03           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 3.84/4.03  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 3.84/4.03  thf(zf_stmt_1, axiom,
% 3.84/4.03    (![B:$i,A:$i]:
% 3.84/4.03     ( ( zip_tseitin_5 @ B @ A ) <=>
% 3.84/4.03       ( ( m1_subset_1 @
% 3.84/4.03           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.84/4.03         ( zip_tseitin_4 @ B @ A ) ) ))).
% 3.84/4.03  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 3.84/4.03  thf(zf_stmt_3, axiom,
% 3.84/4.03    (![B:$i,A:$i]:
% 3.84/4.03     ( ( zip_tseitin_4 @ B @ A ) <=>
% 3.84/4.03       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 3.84/4.03         ( r2_hidden @
% 3.84/4.03           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 3.84/4.03  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 3.84/4.03  thf(zf_stmt_5, axiom,
% 3.84/4.03    (![B:$i,A:$i]:
% 3.84/4.03     ( ( zip_tseitin_3 @ B @ A ) <=>
% 3.84/4.03       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.84/4.03         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 3.84/4.03  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 3.84/4.03  thf(zf_stmt_7, axiom,
% 3.84/4.03    (![C:$i,B:$i,A:$i]:
% 3.84/4.03     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 3.84/4.03       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.84/4.03         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 3.84/4.03  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.84/4.03  thf(zf_stmt_9, axiom,
% 3.84/4.03    (![C:$i,B:$i,A:$i]:
% 3.84/4.03     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 3.84/4.03       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 3.84/4.03         ( r2_hidden @
% 3.84/4.03           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 3.84/4.03  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 3.84/4.03  thf(zf_stmt_11, axiom,
% 3.84/4.03    (![C:$i,B:$i,A:$i]:
% 3.84/4.03     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 3.84/4.03       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 3.84/4.03         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 3.84/4.03  thf(zf_stmt_12, axiom,
% 3.84/4.03    (![A:$i]:
% 3.84/4.03     ( ( l1_pre_topc @ A ) =>
% 3.84/4.03       ( ( v2_pre_topc @ A ) <=>
% 3.84/4.03         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 3.84/4.03           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 3.84/4.03           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 3.84/4.03  thf('0', plain,
% 3.84/4.03      (![X45 : $i]:
% 3.84/4.03         (~ (v2_pre_topc @ X45)
% 3.84/4.03          | (r2_hidden @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45))
% 3.84/4.03          | ~ (l1_pre_topc @ X45))),
% 3.84/4.03      inference('cnf', [status(esa)], [zf_stmt_12])).
% 3.84/4.03  thf(d3_tarski, axiom,
% 3.84/4.03    (![A:$i,B:$i]:
% 3.84/4.03     ( ( r1_tarski @ A @ B ) <=>
% 3.84/4.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.84/4.03  thf('1', plain,
% 3.84/4.03      (![X4 : $i, X6 : $i]:
% 3.84/4.03         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.84/4.03      inference('cnf', [status(esa)], [d3_tarski])).
% 3.84/4.03  thf(d4_tarski, axiom,
% 3.84/4.03    (![A:$i,B:$i]:
% 3.84/4.03     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 3.84/4.03       ( ![C:$i]:
% 3.84/4.03         ( ( r2_hidden @ C @ B ) <=>
% 3.84/4.03           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 3.84/4.03  thf('2', plain,
% 3.84/4.03      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.84/4.03         (~ (r2_hidden @ X10 @ X11)
% 3.84/4.03          | ~ (r2_hidden @ X12 @ X10)
% 3.84/4.03          | (r2_hidden @ X12 @ X13)
% 3.84/4.03          | ((X13) != (k3_tarski @ X11)))),
% 3.84/4.03      inference('cnf', [status(esa)], [d4_tarski])).
% 3.84/4.03  thf('3', plain,
% 3.84/4.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.84/4.03         ((r2_hidden @ X12 @ (k3_tarski @ X11))
% 3.84/4.03          | ~ (r2_hidden @ X12 @ X10)
% 3.84/4.03          | ~ (r2_hidden @ X10 @ X11))),
% 3.84/4.03      inference('simplify', [status(thm)], ['2'])).
% 3.84/4.03  thf('4', plain,
% 3.84/4.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.84/4.03         ((r1_tarski @ X0 @ X1)
% 3.84/4.03          | ~ (r2_hidden @ X0 @ X2)
% 3.84/4.03          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 3.84/4.03      inference('sup-', [status(thm)], ['1', '3'])).
% 3.84/4.03  thf('5', plain,
% 3.84/4.03      (![X0 : $i, X1 : $i]:
% 3.84/4.03         (~ (l1_pre_topc @ X0)
% 3.84/4.03          | ~ (v2_pre_topc @ X0)
% 3.84/4.03          | (r2_hidden @ (sk_C @ X1 @ (u1_struct_0 @ X0)) @ 
% 3.84/4.03             (k3_tarski @ (u1_pre_topc @ X0)))
% 3.84/4.03          | (r1_tarski @ (u1_struct_0 @ X0) @ X1))),
% 3.84/4.03      inference('sup-', [status(thm)], ['0', '4'])).
% 3.84/4.03  thf('6', plain,
% 3.84/4.03      (![X4 : $i, X6 : $i]:
% 3.84/4.03         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 3.84/4.03      inference('cnf', [status(esa)], [d3_tarski])).
% 3.84/4.03  thf('7', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         ((r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0)))
% 3.84/4.03          | ~ (v2_pre_topc @ X0)
% 3.84/4.03          | ~ (l1_pre_topc @ X0)
% 3.84/4.03          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 3.84/4.03      inference('sup-', [status(thm)], ['5', '6'])).
% 3.84/4.03  thf('8', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (~ (l1_pre_topc @ X0)
% 3.84/4.03          | ~ (v2_pre_topc @ X0)
% 3.84/4.03          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 3.84/4.03      inference('simplify', [status(thm)], ['7'])).
% 3.84/4.03  thf(dt_u1_pre_topc, axiom,
% 3.84/4.03    (![A:$i]:
% 3.84/4.03     ( ( l1_pre_topc @ A ) =>
% 3.84/4.03       ( m1_subset_1 @
% 3.84/4.03         ( u1_pre_topc @ A ) @ 
% 3.84/4.03         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 3.84/4.03  thf('9', plain,
% 3.84/4.03      (![X48 : $i]:
% 3.84/4.03         ((m1_subset_1 @ (u1_pre_topc @ X48) @ 
% 3.84/4.03           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48))))
% 3.84/4.03          | ~ (l1_pre_topc @ X48))),
% 3.84/4.03      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 3.84/4.03  thf(t3_subset, axiom,
% 3.84/4.03    (![A:$i,B:$i]:
% 3.84/4.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.84/4.03  thf('10', plain,
% 3.84/4.03      (![X20 : $i, X21 : $i]:
% 3.84/4.03         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 3.84/4.03      inference('cnf', [status(esa)], [t3_subset])).
% 3.84/4.03  thf('11', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (~ (l1_pre_topc @ X0)
% 3.84/4.03          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 3.84/4.03             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 3.84/4.03      inference('sup-', [status(thm)], ['9', '10'])).
% 3.84/4.03  thf(t95_zfmisc_1, axiom,
% 3.84/4.03    (![A:$i,B:$i]:
% 3.84/4.03     ( ( r1_tarski @ A @ B ) =>
% 3.84/4.03       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 3.84/4.03  thf('12', plain,
% 3.84/4.03      (![X17 : $i, X18 : $i]:
% 3.84/4.03         ((r1_tarski @ (k3_tarski @ X17) @ (k3_tarski @ X18))
% 3.84/4.03          | ~ (r1_tarski @ X17 @ X18))),
% 3.84/4.03      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 3.84/4.03  thf('13', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (~ (l1_pre_topc @ X0)
% 3.84/4.03          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 3.84/4.03             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 3.84/4.03      inference('sup-', [status(thm)], ['11', '12'])).
% 3.84/4.03  thf(t99_zfmisc_1, axiom,
% 3.84/4.03    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 3.84/4.03  thf('14', plain, (![X19 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X19)) = (X19))),
% 3.84/4.03      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 3.84/4.03  thf('15', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (~ (l1_pre_topc @ X0)
% 3.84/4.03          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 3.84/4.03      inference('demod', [status(thm)], ['13', '14'])).
% 3.84/4.03  thf(d10_xboole_0, axiom,
% 3.84/4.03    (![A:$i,B:$i]:
% 3.84/4.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.84/4.03  thf('16', plain,
% 3.84/4.03      (![X7 : $i, X9 : $i]:
% 3.84/4.03         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.84/4.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.84/4.03  thf('17', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (~ (l1_pre_topc @ X0)
% 3.84/4.03          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 3.84/4.03               (k3_tarski @ (u1_pre_topc @ X0)))
% 3.84/4.03          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0))))),
% 3.84/4.03      inference('sup-', [status(thm)], ['15', '16'])).
% 3.84/4.03  thf('18', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (~ (v2_pre_topc @ X0)
% 3.84/4.03          | ~ (l1_pre_topc @ X0)
% 3.84/4.03          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 3.84/4.03          | ~ (l1_pre_topc @ X0))),
% 3.84/4.03      inference('sup-', [status(thm)], ['8', '17'])).
% 3.84/4.03  thf('19', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 3.84/4.03          | ~ (l1_pre_topc @ X0)
% 3.84/4.03          | ~ (v2_pre_topc @ X0))),
% 3.84/4.03      inference('simplify', [status(thm)], ['18'])).
% 3.84/4.03  thf('20', plain,
% 3.84/4.03      (![X45 : $i]:
% 3.84/4.03         (~ (v2_pre_topc @ X45)
% 3.84/4.03          | (r2_hidden @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45))
% 3.84/4.03          | ~ (l1_pre_topc @ X45))),
% 3.84/4.03      inference('cnf', [status(esa)], [zf_stmt_12])).
% 3.84/4.03  thf('21', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 3.84/4.03          | ~ (l1_pre_topc @ X0)
% 3.84/4.03          | ~ (v2_pre_topc @ X0))),
% 3.84/4.03      inference('simplify', [status(thm)], ['18'])).
% 3.84/4.03  thf(t14_yellow_1, axiom,
% 3.84/4.03    (![A:$i]:
% 3.84/4.03     ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.84/4.03       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 3.84/4.03         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 3.84/4.03  thf('22', plain,
% 3.84/4.03      (![X49 : $i]:
% 3.84/4.03         (~ (r2_hidden @ (k3_tarski @ X49) @ X49)
% 3.84/4.03          | ((k4_yellow_0 @ (k2_yellow_1 @ X49)) = (k3_tarski @ X49))
% 3.84/4.03          | (v1_xboole_0 @ X49))),
% 3.84/4.03      inference('cnf', [status(esa)], [t14_yellow_1])).
% 3.84/4.03  thf(d1_xboole_0, axiom,
% 3.84/4.03    (![A:$i]:
% 3.84/4.03     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.84/4.03  thf('23', plain,
% 3.84/4.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.84/4.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.84/4.03  thf('24', plain,
% 3.84/4.03      (![X49 : $i]:
% 3.84/4.03         (((k4_yellow_0 @ (k2_yellow_1 @ X49)) = (k3_tarski @ X49))
% 3.84/4.03          | ~ (r2_hidden @ (k3_tarski @ X49) @ X49))),
% 3.84/4.03      inference('clc', [status(thm)], ['22', '23'])).
% 3.84/4.03  thf('25', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 3.84/4.03          | ~ (v2_pre_topc @ X0)
% 3.84/4.03          | ~ (l1_pre_topc @ X0)
% 3.84/4.03          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 3.84/4.03              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 3.84/4.03      inference('sup-', [status(thm)], ['21', '24'])).
% 3.84/4.03  thf('26', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (~ (l1_pre_topc @ X0)
% 3.84/4.03          | ~ (v2_pre_topc @ X0)
% 3.84/4.03          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 3.84/4.03              = (k3_tarski @ (u1_pre_topc @ X0)))
% 3.84/4.03          | ~ (l1_pre_topc @ X0)
% 3.84/4.03          | ~ (v2_pre_topc @ X0))),
% 3.84/4.03      inference('sup-', [status(thm)], ['20', '25'])).
% 3.84/4.03  thf('27', plain,
% 3.84/4.03      (![X0 : $i]:
% 3.84/4.03         (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 3.84/4.03            = (k3_tarski @ (u1_pre_topc @ X0)))
% 3.84/4.03          | ~ (v2_pre_topc @ X0)
% 3.84/4.03          | ~ (l1_pre_topc @ X0))),
% 3.84/4.03      inference('simplify', [status(thm)], ['26'])).
% 3.84/4.03  thf(t24_yellow_1, conjecture,
% 3.84/4.03    (![A:$i]:
% 3.84/4.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.84/4.03       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 3.84/4.03         ( u1_struct_0 @ A ) ) ))).
% 3.84/4.03  thf(zf_stmt_13, negated_conjecture,
% 3.84/4.03    (~( ![A:$i]:
% 3.84/4.03        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.84/4.03            ( l1_pre_topc @ A ) ) =>
% 3.84/4.03          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 3.84/4.03            ( u1_struct_0 @ A ) ) ) )),
% 3.84/4.03    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 3.84/4.03  thf('28', plain,
% 3.84/4.03      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 3.84/4.03         != (u1_struct_0 @ sk_A))),
% 3.84/4.03      inference('cnf', [status(esa)], [zf_stmt_13])).
% 3.84/4.03  thf('29', plain,
% 3.84/4.03      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 3.84/4.03        | ~ (l1_pre_topc @ sk_A)
% 3.84/4.03        | ~ (v2_pre_topc @ sk_A))),
% 3.84/4.03      inference('sup-', [status(thm)], ['27', '28'])).
% 3.84/4.03  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 3.84/4.03      inference('cnf', [status(esa)], [zf_stmt_13])).
% 3.84/4.03  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 3.84/4.03      inference('cnf', [status(esa)], [zf_stmt_13])).
% 3.84/4.03  thf('32', plain,
% 3.84/4.03      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 3.84/4.03      inference('demod', [status(thm)], ['29', '30', '31'])).
% 3.84/4.03  thf('33', plain,
% 3.84/4.03      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 3.84/4.03        | ~ (v2_pre_topc @ sk_A)
% 3.84/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.84/4.03      inference('sup-', [status(thm)], ['19', '32'])).
% 3.84/4.03  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 3.84/4.03      inference('cnf', [status(esa)], [zf_stmt_13])).
% 3.84/4.03  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 3.84/4.03      inference('cnf', [status(esa)], [zf_stmt_13])).
% 3.84/4.03  thf('36', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 3.84/4.03      inference('demod', [status(thm)], ['33', '34', '35'])).
% 3.84/4.03  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 3.84/4.03  
% 3.84/4.03  % SZS output end Refutation
% 3.84/4.03  
% 3.84/4.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
