%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3tA0DuLP5s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 166 expanded)
%              Number of leaves         :   24 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  484 (1455 expanded)
%              Number of equality atoms :   26 (  59 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
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
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_tex_2,axiom,(
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
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X2 )
        = X1 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('13',plain,
    ( ( k1_xboole_0
      = ( sk_C @ k1_xboole_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( k1_xboole_0
    = ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v3_pre_topc @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( k1_xboole_0
    = ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( v3_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('31',plain,(
    v3_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('33',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X19 )
       != ( sk_C @ X16 @ X17 ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( k1_xboole_0
    = ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('46',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['4','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3tA0DuLP5s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 76 iterations in 0.067s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(t35_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.53                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.20/0.53  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(l13_xboole_0, axiom,
% 0.20/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.53  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf(t4_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(d5_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.53             ( ![C:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.20/0.53                      ( ![D:$i]:
% 0.20/0.53                        ( ( m1_subset_1 @
% 0.20/0.53                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.53                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.53                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | (r1_tarski @ (sk_C @ X16 @ X17) @ X16)
% 0.20/0.53          | (v2_tex_2 @ X16 @ X17)
% 0.20/0.53          | ~ (l1_pre_topc @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.53          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X1 @ X2) = (X1)) | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ((k3_xboole_0 @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.53              = (sk_C @ k1_xboole_0 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf(t2_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ((k1_xboole_0) = (sk_C @ k1_xboole_0 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((((k1_xboole_0) = (sk_C @ k1_xboole_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain, (((k1_xboole_0) = (sk_C @ k1_xboole_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | (m1_subset_1 @ (sk_C @ X16 @ X17) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | (v2_tex_2 @ X16 @ X17)
% 0.20/0.53          | ~ (l1_pre_topc @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.53          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf(cc1_tops_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.53          | (v3_pre_topc @ X14 @ X15)
% 0.20/0.53          | ~ (v1_xboole_0 @ X14)
% 0.20/0.53          | ~ (l1_pre_topc @ X15)
% 0.20/0.53          | ~ (v2_pre_topc @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))
% 0.20/0.53          | (v3_pre_topc @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v3_pre_topc @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.53          | ~ (v1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))
% 0.20/0.53          | ~ (v2_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | (v3_pre_topc @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.53  thf('23', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain, (((k1_xboole_0) = (sk_C @ k1_xboole_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | (v3_pre_topc @ k1_xboole_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 0.20/0.53  thf('30', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf('31', plain, ((v3_pre_topc @ k1_xboole_0 @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.53          | ~ (v3_pre_topc @ X19 @ X17)
% 0.20/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X19)
% 0.20/0.53              != (sk_C @ X16 @ X17))
% 0.20/0.53          | (v2_tex_2 @ X16 @ X17)
% 0.20/0.53          | ~ (l1_pre_topc @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.20/0.53              != (sk_C @ k1_xboole_0 @ X0))
% 0.20/0.53          | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.20/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.53              != (sk_C @ k1_xboole_0 @ X0))
% 0.20/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.20/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.20/0.53           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.20/0.53          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.20/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['36', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.20/0.53        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '42'])).
% 0.20/0.53  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain, (((k1_xboole_0) = (sk_C @ k1_xboole_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.53  thf('47', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.53  thf('48', plain, ($false), inference('demod', [status(thm)], ['4', '47'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
