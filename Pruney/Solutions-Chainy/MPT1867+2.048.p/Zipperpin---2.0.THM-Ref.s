%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UQASHhRcfG

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:32 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 108 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  487 ( 790 expanded)
%              Number of equality atoms :   32 (  38 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d6_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X23 )
       != ( sk_C @ X20 @ X21 ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','31'])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( sk_C @ X20 @ X21 ) @ X20 )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35','47'])).

thf('49',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['4','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UQASHhRcfG
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 1482 iterations in 0.628s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.08  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.90/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.08  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.08  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.90/1.08  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(t35_tex_2, conjecture,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( ( v1_xboole_0 @ B ) & 
% 0.90/1.08             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.08           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i]:
% 0.90/1.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.90/1.08            ( l1_pre_topc @ A ) ) =>
% 0.90/1.08          ( ![B:$i]:
% 0.90/1.08            ( ( ( v1_xboole_0 @ B ) & 
% 0.90/1.08                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.08              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.90/1.08  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(l13_xboole_0, axiom,
% 0.90/1.08    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.08  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.08  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.08      inference('demod', [status(thm)], ['0', '3'])).
% 0.90/1.08  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.08  thf(t4_subset_1, axiom,
% 0.90/1.08    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.08      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.08  thf(cc2_pre_topc, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X18 : $i, X19 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.90/1.08          | (v4_pre_topc @ X18 @ X19)
% 0.90/1.08          | ~ (v1_xboole_0 @ X18)
% 0.90/1.08          | ~ (l1_pre_topc @ X19)
% 0.90/1.08          | ~ (v2_pre_topc @ X19))),
% 0.90/1.08      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (v1_xboole_0 @ X1)
% 0.90/1.08          | ~ (v2_pre_topc @ X0)
% 0.90/1.08          | ~ (l1_pre_topc @ X0)
% 0.90/1.08          | ~ (v1_xboole_0 @ X1)
% 0.90/1.08          | (v4_pre_topc @ X1 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((v4_pre_topc @ X1 @ X0)
% 0.90/1.08          | ~ (l1_pre_topc @ X0)
% 0.90/1.08          | ~ (v2_pre_topc @ X0)
% 0.90/1.08          | ~ (v1_xboole_0 @ X1))),
% 0.90/1.08      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v1_xboole_0 @ X0)
% 0.90/1.08          | ~ (v2_pre_topc @ sk_A)
% 0.90/1.08          | (v4_pre_topc @ X0 @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['5', '11'])).
% 0.90/1.08  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.90/1.08      inference('demod', [status(thm)], ['12', '13'])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.08      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.08      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.08  thf(d6_tex_2, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( l1_pre_topc @ A ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08           ( ( v2_tex_2 @ B @ A ) <=>
% 0.90/1.08             ( ![C:$i]:
% 0.90/1.08               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.90/1.08                      ( ![D:$i]:
% 0.90/1.08                        ( ( m1_subset_1 @
% 0.90/1.08                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.90/1.08                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.90/1.08                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.90/1.08          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.90/1.08          | ~ (v4_pre_topc @ X23 @ X21)
% 0.90/1.08          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X23)
% 0.90/1.08              != (sk_C @ X20 @ X21))
% 0.90/1.08          | (v2_tex_2 @ X20 @ X21)
% 0.90/1.08          | ~ (l1_pre_topc @ X21))),
% 0.90/1.08      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (l1_pre_topc @ X0)
% 0.90/1.08          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.08          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.90/1.08              != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.08          | ~ (v4_pre_topc @ X1 @ X0)
% 0.90/1.08          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.90/1.08          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.90/1.08              != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.08          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.08          | ~ (l1_pre_topc @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['15', '18'])).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.08      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.08  thf(redefinition_k9_subset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.08       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.90/1.08  thf('21', plain,
% 0.90/1.08      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.08         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.90/1.08          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.90/1.08           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.08  thf(t3_boole, axiom,
% 0.90/1.08    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.08  thf('23', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.90/1.08      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.08  thf(t48_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.90/1.08  thf('24', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i]:
% 0.90/1.08         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.90/1.08           = (k3_xboole_0 @ X9 @ X10))),
% 0.90/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['23', '24'])).
% 0.90/1.08  thf(d10_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.08  thf('27', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.90/1.08      inference('simplify', [status(thm)], ['26'])).
% 0.90/1.08  thf(l32_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X4 : $i, X6 : $i]:
% 0.90/1.08         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.90/1.08      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.08  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.08  thf('30', plain,
% 0.90/1.08      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.08      inference('demod', [status(thm)], ['25', '29'])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.08      inference('demod', [status(thm)], ['22', '30'])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.90/1.08          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.08          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.08          | ~ (l1_pre_topc @ X0))),
% 0.90/1.08      inference('demod', [status(thm)], ['19', '31'])).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.08        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.08        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.90/1.08        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['14', '32'])).
% 0.90/1.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.08  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.08  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.08      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.08  thf('37', plain,
% 0.90/1.08      (![X20 : $i, X21 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.90/1.08          | (r1_tarski @ (sk_C @ X20 @ X21) @ X20)
% 0.90/1.08          | (v2_tex_2 @ X20 @ X21)
% 0.90/1.08          | ~ (l1_pre_topc @ X21))),
% 0.90/1.08      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.90/1.08  thf('38', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (l1_pre_topc @ X0)
% 0.90/1.08          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.08          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['36', '37'])).
% 0.90/1.08  thf(t3_xboole_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.08  thf('39', plain,
% 0.90/1.08      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.90/1.08  thf('40', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.08          | ~ (l1_pre_topc @ X0)
% 0.90/1.08          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.08  thf('41', plain,
% 0.90/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.08  thf('42', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.08      inference('demod', [status(thm)], ['0', '3'])).
% 0.90/1.08  thf('43', plain,
% 0.90/1.08      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['41', '42'])).
% 0.90/1.08  thf('44', plain,
% 0.90/1.08      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.90/1.08        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.08        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['40', '43'])).
% 0.90/1.08  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.08  thf('47', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.90/1.08      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.90/1.08  thf('48', plain,
% 0.90/1.08      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.90/1.08      inference('demod', [status(thm)], ['33', '34', '35', '47'])).
% 0.90/1.08  thf('49', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.08      inference('simplify', [status(thm)], ['48'])).
% 0.90/1.08  thf('50', plain, ($false), inference('demod', [status(thm)], ['4', '49'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
