%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s4WgA6YrRU

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:30 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 113 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  489 ( 814 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
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
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
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
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X20 )
       != ( sk_C @ X17 @ X18 ) )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34','48'])).

thf('50',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['4','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s4WgA6YrRU
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.06  % Solved by: fo/fo7.sh
% 0.83/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.06  % done 1767 iterations in 0.597s
% 0.83/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.06  % SZS output start Refutation
% 0.83/1.06  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.83/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.83/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.83/1.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.83/1.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.06  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.83/1.06  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.83/1.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.06  thf(t35_tex_2, conjecture,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( ( v1_xboole_0 @ B ) & 
% 0.83/1.06             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.83/1.06           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.83/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.06    (~( ![A:$i]:
% 0.83/1.06        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.83/1.06            ( l1_pre_topc @ A ) ) =>
% 0.83/1.06          ( ![B:$i]:
% 0.83/1.06            ( ( ( v1_xboole_0 @ B ) & 
% 0.83/1.06                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.83/1.06              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.83/1.06    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.83/1.06  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf(l13_xboole_0, axiom,
% 0.83/1.06    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.83/1.06  thf('2', plain,
% 0.83/1.06      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['1', '2'])).
% 0.83/1.06  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.83/1.06      inference('demod', [status(thm)], ['0', '3'])).
% 0.83/1.06  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('6', plain,
% 0.83/1.06      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf(t4_subset_1, axiom,
% 0.83/1.06    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.83/1.06  thf('7', plain,
% 0.83/1.06      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.83/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.83/1.06  thf('8', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['6', '7'])).
% 0.83/1.06  thf(cc2_pre_topc, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.83/1.06  thf('9', plain,
% 0.83/1.06      (![X15 : $i, X16 : $i]:
% 0.83/1.06         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.83/1.06          | (v4_pre_topc @ X15 @ X16)
% 0.83/1.06          | ~ (v1_xboole_0 @ X15)
% 0.83/1.06          | ~ (l1_pre_topc @ X16)
% 0.83/1.06          | ~ (v2_pre_topc @ X16))),
% 0.83/1.06      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.83/1.06  thf('10', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ X1)
% 0.83/1.06          | ~ (v2_pre_topc @ X0)
% 0.83/1.06          | ~ (l1_pre_topc @ X0)
% 0.83/1.06          | ~ (v1_xboole_0 @ X1)
% 0.83/1.06          | (v4_pre_topc @ X1 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.83/1.06  thf('11', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         ((v4_pre_topc @ X1 @ X0)
% 0.83/1.06          | ~ (l1_pre_topc @ X0)
% 0.83/1.06          | ~ (v2_pre_topc @ X0)
% 0.83/1.06          | ~ (v1_xboole_0 @ X1))),
% 0.83/1.06      inference('simplify', [status(thm)], ['10'])).
% 0.83/1.06  thf('12', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ X0)
% 0.83/1.06          | ~ (v2_pre_topc @ sk_A)
% 0.83/1.06          | (v4_pre_topc @ X0 @ sk_A))),
% 0.83/1.06      inference('sup-', [status(thm)], ['5', '11'])).
% 0.83/1.06  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('14', plain,
% 0.83/1.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.83/1.06      inference('demod', [status(thm)], ['12', '13'])).
% 0.83/1.06  thf('15', plain,
% 0.83/1.06      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.83/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.83/1.06  thf('16', plain,
% 0.83/1.06      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.83/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.83/1.06  thf(d6_tex_2, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( l1_pre_topc @ A ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06           ( ( v2_tex_2 @ B @ A ) <=>
% 0.83/1.06             ( ![C:$i]:
% 0.83/1.06               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.83/1.06                      ( ![D:$i]:
% 0.83/1.06                        ( ( m1_subset_1 @
% 0.83/1.06                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.06                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.83/1.06                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.83/1.06                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.06  thf('17', plain,
% 0.83/1.06      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.83/1.06         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.83/1.06          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.83/1.06          | ~ (v4_pre_topc @ X20 @ X18)
% 0.83/1.06          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X20)
% 0.83/1.06              != (sk_C @ X17 @ X18))
% 0.83/1.06          | (v2_tex_2 @ X17 @ X18)
% 0.83/1.06          | ~ (l1_pre_topc @ X18))),
% 0.83/1.06      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.83/1.06  thf('18', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (~ (l1_pre_topc @ X0)
% 0.83/1.06          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.83/1.06          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.83/1.06              != (sk_C @ k1_xboole_0 @ X0))
% 0.83/1.06          | ~ (v4_pre_topc @ X1 @ X0)
% 0.83/1.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.83/1.06      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.06  thf('19', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.83/1.06          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.83/1.06              != (sk_C @ k1_xboole_0 @ X0))
% 0.83/1.06          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.83/1.06          | ~ (l1_pre_topc @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['15', '18'])).
% 0.83/1.06  thf('20', plain,
% 0.83/1.06      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.83/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.83/1.06  thf(redefinition_k9_subset_1, axiom,
% 0.83/1.06    (![A:$i,B:$i,C:$i]:
% 0.83/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.06       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.83/1.06  thf('21', plain,
% 0.83/1.06      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.83/1.06         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.83/1.06          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.83/1.06      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.83/1.06  thf('22', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.83/1.06           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.83/1.06  thf(t48_xboole_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.83/1.06  thf('23', plain,
% 0.83/1.06      (![X6 : $i, X7 : $i]:
% 0.83/1.06         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.83/1.06           = (k3_xboole_0 @ X6 @ X7))),
% 0.83/1.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.06  thf(t36_xboole_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.83/1.06  thf('24', plain,
% 0.83/1.06      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.83/1.06      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.83/1.06  thf('25', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.83/1.06      inference('sup+', [status(thm)], ['23', '24'])).
% 0.83/1.06  thf(t3_xboole_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.83/1.06  thf('26', plain,
% 0.83/1.06      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.83/1.06      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.83/1.06  thf('27', plain,
% 0.83/1.06      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['25', '26'])).
% 0.83/1.06  thf(commutativity_k3_xboole_0, axiom,
% 0.83/1.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.83/1.06  thf('28', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.83/1.06  thf('29', plain,
% 0.83/1.06      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['27', '28'])).
% 0.83/1.06  thf('30', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.06      inference('demod', [status(thm)], ['22', '29'])).
% 0.83/1.06  thf('31', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.83/1.06          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.83/1.06          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.83/1.06          | ~ (l1_pre_topc @ X0))),
% 0.83/1.06      inference('demod', [status(thm)], ['19', '30'])).
% 0.83/1.06  thf('32', plain,
% 0.83/1.06      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.06        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.83/1.06        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['14', '31'])).
% 0.83/1.06  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.06  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.06  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('35', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['6', '7'])).
% 0.83/1.06  thf('36', plain,
% 0.83/1.06      (![X17 : $i, X18 : $i]:
% 0.83/1.06         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.83/1.06          | (r1_tarski @ (sk_C @ X17 @ X18) @ X17)
% 0.83/1.06          | (v2_tex_2 @ X17 @ X18)
% 0.83/1.06          | ~ (l1_pre_topc @ X18))),
% 0.83/1.06      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.83/1.06  thf('37', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ X1)
% 0.83/1.06          | ~ (l1_pre_topc @ X0)
% 0.83/1.06          | (v2_tex_2 @ X1 @ X0)
% 0.83/1.06          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 0.83/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.83/1.06  thf('38', plain,
% 0.83/1.06      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.83/1.06      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.83/1.06  thf('39', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.83/1.06          | ~ (l1_pre_topc @ X0)
% 0.83/1.06          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.06          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['37', '38'])).
% 0.83/1.06  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.06  thf('41', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.83/1.06          | ~ (l1_pre_topc @ X0)
% 0.83/1.06          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['39', '40'])).
% 0.83/1.06  thf('42', plain,
% 0.83/1.06      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf('43', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.83/1.06      inference('demod', [status(thm)], ['0', '3'])).
% 0.83/1.06  thf('44', plain,
% 0.83/1.06      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['42', '43'])).
% 0.83/1.06  thf('45', plain,
% 0.83/1.06      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.83/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.06        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['41', '44'])).
% 0.83/1.06  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.06  thf('48', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.83/1.06      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.83/1.06  thf('49', plain,
% 0.83/1.06      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['32', '33', '34', '48'])).
% 0.83/1.06  thf('50', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.83/1.06      inference('simplify', [status(thm)], ['49'])).
% 0.83/1.06  thf('51', plain, ($false), inference('demod', [status(thm)], ['4', '50'])).
% 0.83/1.06  
% 0.83/1.06  % SZS output end Refutation
% 0.83/1.06  
% 0.83/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
