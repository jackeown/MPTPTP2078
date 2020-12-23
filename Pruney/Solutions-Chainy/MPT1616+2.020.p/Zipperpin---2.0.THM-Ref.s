%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PHcNyljva4

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 125 expanded)
%              Number of leaves         :   46 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  552 ( 930 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X38: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ( r2_hidden @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ ( k1_zfmisc_1 @ ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X41 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X7 ) @ ( k3_tarski @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X9: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X9 ) )
      = X9 ) ),
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
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
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
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X38: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ( r2_hidden @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('22',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X42 ) @ X42 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X42 ) )
        = ( k3_tarski @ X42 ) )
      | ( v1_xboole_0 @ X42 ) ) ),
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
    ! [X42: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X42 ) )
        = ( k3_tarski @ X42 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X42 ) @ X42 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PHcNyljva4
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:02:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 133 iterations in 0.078s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.53  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.53  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.20/0.53  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(d1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.53         ( ( ![B:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ![C:$i]:
% 0.20/0.53                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.53                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.53                     ( r2_hidden @
% 0.20/0.53                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.20/0.53                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.20/0.53           ( ![B:$i]:
% 0.20/0.53             ( ( m1_subset_1 @
% 0.20/0.53                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.53                 ( r2_hidden @
% 0.20/0.53                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.53                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.20/0.53           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_1, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.20/0.53       ( ( m1_subset_1 @
% 0.20/0.53           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.20/0.53  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_3, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.20/0.53       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.53         ( r2_hidden @
% 0.20/0.53           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_5, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.20/0.53       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_7, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.20/0.53       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.20/0.53  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_9, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.20/0.53       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.53         ( r2_hidden @
% 0.20/0.53           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_11, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.20/0.53       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.53         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_12, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.53         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.53           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.20/0.53           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X38 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ X38)
% 0.20/0.53          | (r2_hidden @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))
% 0.20/0.53          | ~ (l1_pre_topc @ X38))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.20/0.53  thf(t100_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X6 : $i]: (r1_tarski @ X6 @ (k1_zfmisc_1 @ (k3_tarski @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X10 : $i, X12 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf(t4_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X13 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.20/0.53          | (m1_subset_1 @ X13 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (k3_tarski @ (u1_pre_topc @ X0)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf(dt_u1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( m1_subset_1 @
% 0.20/0.53         ( u1_pre_topc @ A ) @ 
% 0.20/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X41 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (u1_pre_topc @ X41) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41))))
% 0.20/0.53          | ~ (l1_pre_topc @ X41))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf(t95_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.53       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         ((r1_tarski @ (k3_tarski @ X7) @ (k3_tarski @ X8))
% 0.20/0.53          | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.20/0.53             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf(t99_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.53  thf('14', plain, (![X9 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X9)) = (X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X3 : $i, X5 : $i]:
% 0.20/0.53         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.20/0.53               (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X38 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ X38)
% 0.20/0.53          | (r2_hidden @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))
% 0.20/0.53          | ~ (l1_pre_topc @ X38))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((u1_struct_0 @ X0) = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.53  thf(t14_yellow_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.20/0.53         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X42 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k3_tarski @ X42) @ X42)
% 0.20/0.53          | ((k4_yellow_0 @ (k2_yellow_1 @ X42)) = (k3_tarski @ X42))
% 0.20/0.53          | (v1_xboole_0 @ X42))),
% 0.20/0.53      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.20/0.53  thf(d1_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X42 : $i]:
% 0.20/0.53         (((k4_yellow_0 @ (k2_yellow_1 @ X42)) = (k3_tarski @ X42))
% 0.20/0.53          | ~ (r2_hidden @ (k3_tarski @ X42) @ X42))),
% 0.20/0.53      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.20/0.53              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.20/0.53              = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.20/0.53            = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.53  thf(t24_yellow_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.53         ( u1_struct_0 @ A ) ) ))).
% 0.20/0.53  thf(zf_stmt_13, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.53            ( u1_struct_0 @ A ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.20/0.53         != (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.53  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '32'])).
% 0.20/0.53  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.53  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.53  thf('36', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.53  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
